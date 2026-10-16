#include "common.h"
#include "kcont.h"
#include <string.h>

__thread KCont *kc_tl;
__thread int kc_lock_depth;
__thread int kc_last_counter;

/* continuation threads are reused: a thread whose call completed parks and
 * takes the next continuation (no thread creation per kernel call after the
 * first few; the parked set is a free list) */
typedef struct KWorker { pthread_t thread; pthread_mutex_t mu; pthread_cond_t cv; KCont *k; struct KWorker *next, *all_next; bool stop; } KWorker;
static pthread_mutex_t P_mu = PTHREAD_MUTEX_INITIALIZER;
static KWorker *parked, *all;

static void run_one(KCont *k) {
    kc_tl = k;
    pthread_mutex_lock(&k->mu);
    while (k->state != 1) pthread_cond_wait(&k->cv, &k->mu);   /* the first grant */
    pthread_mutex_unlock(&k->mu);
    k->fn(k);
    require(kc_lock_depth == 0, "kernel continuation completed holding a lock");
    kc_tl = NULL;
    pthread_mutex_lock(&k->mu);
    k->state = 2; pthread_cond_broadcast(&k->cv);
    pthread_mutex_unlock(&k->mu);
}
static void *kc_worker(void *p) {
    KWorker *w = p;
    for (;;) {
        pthread_mutex_lock(&w->mu);
        while (!w->k && !w->stop) pthread_cond_wait(&w->cv, &w->mu);
        if (!w->k) { pthread_mutex_unlock(&w->mu); return NULL; }
        KCont *k = w->k; w->k = NULL;
        pthread_mutex_unlock(&w->mu);
        run_one(k);
        pthread_mutex_lock(&P_mu); w->next = parked; parked = w; pthread_mutex_unlock(&P_mu);   /* park */
    }
}
static void assign(KCont *k) {
    pthread_mutex_lock(&P_mu);
    KWorker *w = parked;
    if (w) parked = w->next;
    else {
        w = calloc(1, sizeof *w); require(w, "out of memory");
        pthread_mutex_init(&w->mu, NULL); pthread_cond_init(&w->cv, NULL);
        w->all_next = all; all = w;
        require(pthread_create(&w->thread, NULL, kc_worker, w) == 0, "kcont: thread");
    }
    pthread_mutex_unlock(&P_mu);
    pthread_mutex_lock(&w->mu); w->k = k; pthread_cond_broadcast(&w->cv); pthread_mutex_unlock(&w->mu);
}

KCont *kc_new(KFn fn, const uint64_t *args, size_t nargs) {
    KCont *k = calloc(1, sizeof *k); require(k, "out of memory");
    pthread_mutex_init(&k->mu, NULL); pthread_cond_init(&k->cv, NULL);
    k->fn = fn; require(nargs <= 6, "kcont args"); for (size_t i = 0; i < nargs; i++) k->arg[i] = args[i];
    k->why = "";
    return k;
}
size_t kc_grant(KCont *k, size_t budget) {
    if (k->state == 2) return 0;
    pthread_mutex_lock(&k->mu);
    k->budget = budget; k->used = 0; k->state = 1;
    pthread_cond_broadcast(&k->cv);
    bool first = !k->started; k->started = true;
    pthread_mutex_unlock(&k->mu);
    if (first) assign(k);
    pthread_mutex_lock(&k->mu);
    while (k->state == 1) pthread_cond_wait(&k->cv, &k->mu);   /* until it yields or completes */
    size_t used = k->used;
    pthread_mutex_unlock(&k->mu);
    return used;
}
bool kc_done(const KCont *k) { return k->state == 2; }
void kc_free(KCont *k) {
    if (!k) return;
    if (k->started) while (k->state != 2) kc_grant(k, KC_UNBOUNDED);
    pthread_mutex_destroy(&k->mu); pthread_cond_destroy(&k->cv); free(k);
}
void kc_shutdown(void) {   /* teardown: every continuation has completed, so every worker is parked or about to park */
    pthread_mutex_lock(&P_mu); KWorker *w = all; all = NULL; parked = NULL; pthread_mutex_unlock(&P_mu);
    while (w) { KWorker *n = w->all_next; pthread_mutex_lock(&w->mu); w->stop = true; pthread_cond_broadcast(&w->cv); pthread_mutex_unlock(&w->mu); pthread_join(w->thread, NULL); pthread_mutex_destroy(&w->mu); pthread_cond_destroy(&w->cv); free(w); w = n; }
}
/* one transition of the running continuation: under a bounded grant, the
 * budget's last transition yields — at the first transition point where the
 * thread holds no mutex (a yield deferred past a locked section adds that
 * section's transitions to the unit; they are counted) */
void kc_tick(void) {
    KCont *k = kc_tl; if (!k) return;
    k->steps++;
    if (k->budget == KC_UNBOUNDED) { k->used++; return; }
    k->used++;
    if (k->used < k->budget) return;
#ifdef KC_TRACE
    static __thread uint64_t deferred[64]; static __thread int dmax;
    if (kc_lock_depth > 0) { deferred[kc_last_counter & 63]++; if (kc_lock_depth > dmax) dmax = kc_lock_depth; return; }
    { uint64_t tot = 0; for (int i = 0; i < 64; i++) tot += deferred[i]; if (tot > 64) { fprintf(stderr, "deferred kind=%llu depth=%d:", (unsigned long long)k->arg[0], dmax); for (int i = 0; i < 64; i++) if (deferred[i]) fprintf(stderr, " c%d=%llu", i, (unsigned long long)deferred[i]); fprintf(stderr, "\n"); } memset(deferred, 0, sizeof deferred); dmax = 0; }
#else
    if (kc_lock_depth > 0) return;
#endif
    pthread_mutex_lock(&k->mu);
    k->state = 0; pthread_cond_broadcast(&k->cv);
    while (k->state != 1) pthread_cond_wait(&k->cv, &k->mu);
    pthread_mutex_unlock(&k->mu);
}
