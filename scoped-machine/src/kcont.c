#include "common.h"
#include "kcont.h"
#include "reuse.h"
#include <string.h>

__thread KCont *kc_tl;
__thread int kc_lock_depth;
__thread int kc_last_counter;

/* continuation threads are reused: a thread whose call completed parks and
 * takes the next continuation (no thread creation per kernel call after the
 * first few; the parked set is a free list) */
typedef struct KWorker { pthread_t thread; pthread_mutex_t mu; pthread_cond_t cv; KCont *k; KCont *running; struct KWorker *next, *all_next; bool stop; } KWorker;
/* continuation records and workers are host allocations (not the machine's
 * arena): an abandoned continuation's parked thread keeps referring to its
 * record after the machine's storage is retired (V21 R5) */
static pthread_mutex_t P_mu = PTHREAD_MUTEX_INITIALIZER;
static KWorker *parked, *all;
KCont *kc_current(void) { return kc_tl; }

static void run_one(KCont *k, pthread_mutex_t *wmu, KCont **wrunning) {
    kc_tl = k;
    pthread_mutex_lock(&k->mu);
    while (k->state != 1) pthread_cond_wait(&k->cv, &k->mu);   /* the first grant */
    pthread_mutex_unlock(&k->mu);
    ReuseScope *prev_acct = reuse_scope_enter(k->acct);
    k->fn(k);
    reuse_scope_leave(prev_acct);
    require(kc_lock_depth == 0, "kernel continuation completed holding a lock");
    if (k->outcome == KO_PENDING) k->outcome = k->ok ? KO_OK : KO_INVALID;
    kc_tl = NULL;
    pthread_mutex_lock(wmu); *wrunning = NULL; pthread_mutex_unlock(wmu);   /* before completion is visible: the record may be freed after it */
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
        KCont *k = w->k; w->k = NULL; w->running = k;
        pthread_mutex_unlock(&w->mu);
        run_one(k, &w->mu, &w->running);
        pthread_mutex_lock(&P_mu); w->next = parked; parked = w; pthread_mutex_unlock(&P_mu);   /* park */
    }
}
static void assign(KCont *k) {
    pthread_mutex_lock(&P_mu);
    KWorker *w = parked;
    if (w) parked = w->next;
    else {
        w = (calloc)(1, sizeof *w); require(w, "out of memory");
        pthread_mutex_init(&w->mu, NULL); pthread_cond_init(&w->cv, NULL);
        w->all_next = all; all = w;
        require(pthread_create(&w->thread, NULL, kc_worker, w) == 0, "kcont: thread");
    }
    pthread_mutex_unlock(&P_mu);
    pthread_mutex_lock(&w->mu); w->k = k; pthread_cond_broadcast(&w->cv); pthread_mutex_unlock(&w->mu);
}

KCont *kc_new(KFn fn, const uint64_t *args, size_t nargs) {
    KCont *k = (calloc)(1, sizeof *k); require(k, "out of memory");
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
    pthread_mutex_destroy(&k->mu); pthread_cond_destroy(&k->cv); (free)(k);
}
/* V21 R5: closed-session destruction of a started continuation that cannot
 * be completed: it is never granted again; its parked thread is detached at
 * shutdown and keeps its record (held no lock at its last yield) */
void kc_abandon(KCont *k) {
    if (!k) return;
    if (!k->started || k->state == 2) { kc_free(k); return; }
    pthread_mutex_lock(&k->mu); k->abandoned = true; pthread_mutex_unlock(&k->mu);
}
void kc_shutdown(void) {   /* teardown: every continuation has completed, so every worker is parked or about to park */
    pthread_mutex_lock(&P_mu); KWorker *w = all; all = NULL; parked = NULL; pthread_mutex_unlock(&P_mu);
    while (w) {
        KWorker *n = w->all_next;
        pthread_mutex_lock(&w->mu); bool abandoned = w->running && w->running->abandoned; w->stop = true; pthread_cond_broadcast(&w->cv); pthread_mutex_unlock(&w->mu);
        if (abandoned) pthread_detach(w->thread);   /* parked forever inside an abandoned continuation: detached, its records kept */
        else { pthread_join(w->thread, NULL); pthread_mutex_destroy(&w->mu); pthread_cond_destroy(&w->cv); (free)(w); }
        w = n;
    }
    /* a worker that finished its continuation during the drain parks itself
     * after its grant returned: the joined workers' park entries are dropped */
    pthread_mutex_lock(&P_mu); parked = NULL; pthread_mutex_unlock(&P_mu);
}
/* one transition of the running continuation: under a bounded grant, the
 * budget's last transition yields — at the first transition point where the
 * thread holds no mutex (a yield deferred past a locked section adds that
 * section's transitions to the unit; they are counted) */
static void yield_now(KCont *k) {
    pthread_mutex_lock(&k->mu);
    k->state = 0; pthread_cond_broadcast(&k->cv);
    while (k->state != 1) pthread_cond_wait(&k->cv, &k->mu);
    pthread_mutex_unlock(&k->mu);
}
void kc_wait_job(pthread_cond_t *cv, pthread_mutex_t *mu, KCont *on, uint64_t on_job) {
    KCont *k = kc_tl;
    if (!k || (k->budget == KC_UNBOUNDED && !on)) { pthread_cond_wait(cv, mu); return; }   /* a plain thread, or a synchronous run waiting on another plain thread */
    /* a continuation: the wait is one transition; it yields with the dependency recorded */
    k->steps++; k->used++;
    k->blocked = true; k->blocked_on = on; k->blocked_job = on ? on_job : 0;
    pthread_mutex_unlock(mu);
    require(kc_lock_depth == 0, "kernel continuation waits while holding another lock");
    yield_now(k);
    k->blocked = false; k->blocked_on = NULL; k->blocked_job = 0;
    pthread_mutex_lock(mu);
}
void kc_wait(pthread_cond_t *cv, pthread_mutex_t *mu, KCont *on) { kc_wait_job(cv, mu, on, on ? on->job : 0); }
void kc_safepoint(void) { KCont *k = kc_tl; if (!k || k->budget == KC_UNBOUNDED || k->used < k->budget || kc_lock_depth > 0) return; yield_now(k); }
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
    yield_now(k);
}

#ifdef KC_LOCK_AUDIT
/* ---- the lock-section audit: per outermost acquisition site, the maximum
 * number of fine steps this thread took while holding it, and the maximum
 * distinct-site count; printed at exit (single-threaded runs give exact
 * per-thread attribution; fine counters are global, so run the audit with
 * CUBICAL_WORKERS=0) ---- */
#include "fine.h"
typedef struct { const char *site; uint64_t max, calls, total; } AuditSite;
static AuditSite audit[512]; static size_t naudit; static pthread_mutex_t audit_mu = PTHREAD_MUTEX_INITIALIZER;
static __thread const char *cur_site; static __thread uint64_t cur_start;
static uint64_t fine_total(void) { return fine_tl_steps; }
void kc_audit_enter(const char *site) { cur_site = site; cur_start = fine_total(); }
static void audit_report(void) {
    fprintf(stderr, "lock-section audit: %zu sites (max fine steps under the outermost lock)\n", naudit);
    for (size_t pass = 0; pass < naudit; pass++) { size_t best = pass; for (size_t j = pass + 1; j < naudit; j++) if (audit[j].max > audit[best].max) best = j; AuditSite t = audit[pass]; audit[pass] = audit[best]; audit[best] = t; }
    for (size_t i = 0; i < naudit; i++) fprintf(stderr, "  %-28s max=%-8llu calls=%-10llu mean=%.2f\n", audit[i].site, (unsigned long long)audit[i].max, (unsigned long long)audit[i].calls, audit[i].calls ? (double)audit[i].total / audit[i].calls : 0.0);
}
void kc_audit_leave(void) {
    uint64_t d = fine_total() - cur_start; const char *site = cur_site; cur_site = NULL;
    (pthread_mutex_lock)(&audit_mu);
    static bool registered; if (!registered) { registered = true; atexit(audit_report); }
    size_t i = 0; while (i < naudit && audit[i].site != site) i++;
    if (i == naudit && naudit < 512) { audit[naudit].site = site; audit[naudit].max = 0; audit[naudit].calls = 0; audit[naudit].total = 0; naudit++; }
    if (i < naudit) { if (d > audit[i].max) audit[i].max = d; audit[i].calls++; audit[i].total += d; }
    (pthread_mutex_unlock)(&audit_mu);
}
#endif
