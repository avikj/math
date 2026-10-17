#include "common.h"
#include "kcont.h"
#include "reuse.h"
#include "kstack.h"
#include <string.h>
#include <setjmp.h>

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
static KOwn *reap_list;                 /* registries of cancelled continuations, reaped after the machine's structures (kc_reap_storage) */
static size_t st_cancelled, st_cleanups, st_reaped, st_workers;
KCont *kc_current(void) { return kc_tl; }
KOwn *kc_owner_current(void) { KCont *k = kc_tl; return k ? k->own : NULL; }
void kc_cleanup_push(KCleanup *c, void (*fn)(void *), void *arg) { KCont *k = kc_tl; c->fn = fn; c->arg = arg; c->prev = NULL; if (!k) return; c->prev = k->cleanups; k->cleanups = c; }
void kc_cleanup_pop(KCleanup *c) { KCont *k = kc_tl; if (!k) return; require(k->cleanups == c, "kcont: cleanup records pop in order"); k->cleanups = c->prev; }
KcStats kc_stats(void) { KcStats s; pthread_mutex_lock(&P_mu); s.cancelled = st_cancelled; s.unwound_cleanups = st_cleanups; s.reaped_allocations = st_reaped; s.live_workers = st_workers; pthread_mutex_unlock(&P_mu); return s; }
/* V23 R3: the cancellation return path. At a resumption point the thread
 * holds no lock (every yield is taken at lock depth 0); the registered
 * releases run innermost first while their frames are still live, then the
 * thread jumps to the innermost unwind target (its segment's entry or the
 * continuation's base) — never across a segment boundary. */
static void kc_unwind(KCont *k) {
    require(kc_lock_depth == 0, "kcont: cancellation at a resumption point holding a lock");
    size_t n = 0;
    for (KCleanup *c = k->cleanups; c; c = c->prev) { c->fn(c->arg); n++; }
    k->cleanups = NULL;
    if (n) { pthread_mutex_lock(&P_mu); st_cleanups += n; pthread_mutex_unlock(&P_mu); }
    longjmp(*(jmp_buf *)kstack_unwind, 1);
}

static void run_one(KCont *k, pthread_mutex_t *wmu, KCont **wrunning) {
    kc_tl = k;
    pthread_mutex_lock(&k->mu);
    while (k->state != 1) pthread_cond_wait(&k->cv, &k->mu);   /* the first grant */
    pthread_mutex_unlock(&k->mu);
    ReuseScope *prev_acct = reuse_scope_enter(k->acct);
    KOwn *own = (calloc)(1, sizeof *own); require(own, "out of memory"); pthread_mutex_init(&own->mu, NULL);
    k->own = own;
    jmp_buf base; void *prev_target = kstack_unwind; kstack_unwind = &base;
    volatile bool cancelled = false;
    if (setjmp(base) == 0) k->fn(k);
    else cancelled = true;                       /* V23 R3: unwound by cancellation; no result is published */
    kstack_unwind = prev_target;
    reuse_scope_leave(prev_acct);
    require(kc_lock_depth == 0, "kernel continuation completed holding a lock");
    k->own = NULL;
    if (cancelled) { pthread_mutex_lock(&P_mu); own->next = reap_list; reap_list = own; pthread_mutex_unlock(&P_mu); }
    else kalloc_release_owner(own);              /* its live allocations belong to whatever retains them */
    if (!cancelled && k->outcome == KO_PENDING) k->outcome = k->ok ? KO_OK : KO_INVALID;
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
        w->all_next = all; all = w; st_workers++;
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
/* V23 R3: closed-session destruction of a started, uncompleted continuation
 * (the closed-session precondition: no client retains it). It is resumed
 * once with `cancel` set: its thread runs the registered releases, unwinds
 * through its stack segments to its base, hands its allocation registry to
 * the reap list and parks; then the record is freed. Nothing is evaluated
 * and no result is published. */
void kc_cancel(KCont *k) {
    if (!k) return;
    if (!k->started || k->state == 2) { kc_free(k); return; }
    pthread_mutex_lock(&k->mu);
    k->cancel = true; k->abandoned = true; k->state = 1; pthread_cond_broadcast(&k->cv);
    while (k->state != 2) pthread_cond_wait(&k->cv, &k->mu);
    pthread_mutex_unlock(&k->mu);
    pthread_mutex_lock(&P_mu); st_cancelled++; pthread_mutex_unlock(&P_mu);
    kc_free(k);
}
void kc_abandon(KCont *k) { kc_cancel(k); }
/* after the machine's own structures are freed: allocations still registered
 * to a cancelled continuation were private to it (anything it had published
 * was freed with the structure retaining it, which unregistered it) */
void kc_reap_storage(void) {
    pthread_mutex_lock(&P_mu); KOwn *o = reap_list; reap_list = NULL; pthread_mutex_unlock(&P_mu);
    while (o) { KOwn *n = o->next; size_t c = kalloc_reap_owner(o); pthread_mutex_lock(&P_mu); st_reaped += c; pthread_mutex_unlock(&P_mu); o = n; }
}
static int live_modules;
void kc_session(int module, bool live) {
    pthread_mutex_lock(&P_mu); if (live) live_modules |= module; else live_modules &= ~module; bool reap = live_modules == 0 && reap_list; pthread_mutex_unlock(&P_mu);
    if (reap) kc_reap_storage();
}
void kc_shutdown(void) {   /* teardown: every continuation has completed or been cancelled, so every worker is parked or about to park */
    pthread_mutex_lock(&P_mu); KWorker *w = all; all = NULL; parked = NULL; pthread_mutex_unlock(&P_mu);
    while (w) {
        KWorker *n = w->all_next;
        pthread_mutex_lock(&w->mu); w->stop = true; pthread_cond_broadcast(&w->cv); pthread_mutex_unlock(&w->mu);
        pthread_join(w->thread, NULL); pthread_mutex_destroy(&w->mu); pthread_cond_destroy(&w->cv); (free)(w);
        pthread_mutex_lock(&P_mu); st_workers--; pthread_mutex_unlock(&P_mu);
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
    bool cancel = k->cancel;
    pthread_mutex_unlock(&k->mu);
    if (cancel) kc_unwind(k);
}
void kc_wait_job(pthread_cond_t *cv, pthread_mutex_t *mu, KCont *on, uint64_t on_job) {
    KCont *k = kc_tl;
    if (!k || (k->budget == KC_UNBOUNDED && !on)) { pthread_cond_wait(cv, mu); return; }   /* a plain thread, or a synchronous run waiting on another plain thread */
    /* a continuation: the wait is one transition; it yields with the dependency recorded */
    xl_add(&k->steps, &k->steps_carry, 1); k->used++;
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
    xl_add(&k->steps, &k->steps_carry, 1);
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
