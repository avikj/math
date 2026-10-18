/* kframe.c — see kframe.h. Frame pages, stack records and the context copies
 * are host allocations: the frames are the control state of the instrumented
 * allocator's callers, not values it serves. */
#include "common.h"
#include "kframe.h"
#include "event.h"
#include "reuse.h"
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

__thread KStack *kf_tl;
__thread int kf_lock_depth;
__thread int kf_last_counter;

#define PAGE_BYTES ((size_t)64 << 10)
struct KFPage { KFPage *prev; size_t used, cap; KFPage *spare; char *mem; };

static struct { pthread_mutex_t mu; uint64_t stacks, frames, grants, suspends, waits, cancelled, dropped, sync_runs, sync_in_step; size_t live_stacks, live_pages, max_depth; } S = { PTHREAD_MUTEX_INITIALIZER, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
#define BUMP(f) __atomic_add_fetch(&S.f, 1, __ATOMIC_RELAXED)
KfStats kf_stats(void) {
    KfStats r;
    r.stacks = __atomic_load_n(&S.stacks, __ATOMIC_RELAXED); r.frames = __atomic_load_n(&S.frames, __ATOMIC_RELAXED);
    r.grants = __atomic_load_n(&S.grants, __ATOMIC_RELAXED); r.suspends = __atomic_load_n(&S.suspends, __ATOMIC_RELAXED);
    r.waits = __atomic_load_n(&S.waits, __ATOMIC_RELAXED); r.cancelled = __atomic_load_n(&S.cancelled, __ATOMIC_RELAXED);
    r.dropped_frames = __atomic_load_n(&S.dropped, __ATOMIC_RELAXED); r.sync_runs = __atomic_load_n(&S.sync_runs, __ATOMIC_RELAXED);
    r.sync_in_step = __atomic_load_n(&S.sync_in_step, __ATOMIC_RELAXED);
    r.live_stacks = __atomic_load_n(&S.live_stacks, __ATOMIC_RELAXED); r.live_pages = __atomic_load_n(&S.live_pages, __ATOMIC_RELAXED); r.max_depth = __atomic_load_n(&S.max_depth, __ATOMIC_RELAXED);
    return r;
}

/* ---- pages ---- */
static KFPage *page_new(size_t need) {
    size_t cap = need > PAGE_BYTES ? need : PAGE_BYTES;
    KFPage *p = (malloc)(sizeof *p); char *m = (malloc)(cap); if (!p || !m) { fprintf(stderr, "fatal: kframe: the host could not supply a frame page\n"); abort(); }
    p->prev = NULL; p->used = 0; p->cap = cap; p->spare = NULL; p->mem = m;
    __atomic_add_fetch(&S.live_pages, 1, __ATOMIC_RELAXED);
    return p;
}
static void page_free(KFPage *p) { (free)(p->mem); (free)(p); __atomic_sub_fetch(&S.live_pages, 1, __ATOMIC_RELAXED); }
static void pages_free(KFPage *p) {
    while (p) { KFPage *prev = p->prev; if (p->spare) page_free(p->spare); page_free(p); p = prev; }
}

void *kf_push(KStack *ks, const KFamily *fam) {
    size_t bytes = (fam->size + 15) & ~(size_t)15;
    KFPage *p = ks->page;
    if (!p || p->used + bytes > p->cap) {
        KFPage *n = NULL;
        if (p && p->spare && p->spare->cap >= bytes) { n = p->spare; p->spare = NULL; }
        else n = page_new(bytes);
        n->prev = p; n->used = 0; ks->page = p = n;
    }
    KF *f = (KF *)(p->mem + p->used); p->used += bytes;
    memset(f, 0, bytes);
    f->fam = fam; f->bytes = (uint32_t)bytes; f->up = ks->top; ks->top = f;
    if (++ks->depth > ks->max_depth) { ks->max_depth = ks->depth; size_t m = __atomic_load_n(&S.max_depth, __ATOMIC_RELAXED); while (m < ks->depth && !__atomic_compare_exchange_n(&S.max_depth, &m, ks->depth, true, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) ; }
    BUMP(frames);
    return f;
}
static void pop(KStack *ks, KF *f) {
    KFPage *p = ks->page;
    ks->top = f->up; ks->depth--;
    p->used -= f->bytes;
    if (p->used == 0 && p->prev) {   /* an emptied page is kept as the spare of the one below it */
        KFPage *below = p->prev; p->prev = NULL;
        if (below->spare) page_free(below->spare);
        if (p->spare) { page_free(p->spare); p->spare = NULL; }
        below->spare = p; ks->page = below;
    }
}

/* ---- computation-local state ---- */
typedef struct { void *(*addr)(void); size_t size, off; const void *init; void (*release)(void *); } Slot;
static Slot slots[32]; static size_t nslots, ctx_bytes;
struct KFCtx { char *bytes; EvSaved units; };
void kf_ctx_register(void *(*addr)(void), size_t size, const void *init, void (*release)(void *copy)) {
    pthread_mutex_lock(&S.mu);
    for (size_t i = 0; i < nslots; i++) if (slots[i].addr == addr) { pthread_mutex_unlock(&S.mu); return; }
    require(nslots < 32, "kframe: computation-local slots exhausted");
    slots[nslots].addr = addr; slots[nslots].size = size; slots[nslots].off = ctx_bytes; slots[nslots].init = init; slots[nslots].release = release;
    ctx_bytes += (size + 15) & ~(size_t)15; nslots++;
    pthread_mutex_unlock(&S.mu);
}
static KFCtx *ctx_new(void) {
    KFCtx *c = (calloc)(1, sizeof *c); if (!c) abort();
    c->bytes = (calloc)(1, ctx_bytes ? ctx_bytes : 1); if (!c->bytes) abort();
    for (size_t i = 0; i < nslots; i++) if (slots[i].init) memcpy(c->bytes + slots[i].off, slots[i].init, slots[i].size);
    return c;
}
static void ctx_swap(KFCtx *c) {
    char tmp[256];
    for (size_t i = 0; i < nslots; i++) {
        char *t = slots[i].addr(), *s = c->bytes + slots[i].off; size_t n = slots[i].size;
        require(n <= sizeof tmp, "kframe: computation-local slot too large");
        memcpy(tmp, t, n); memcpy(t, s, n); memcpy(s, tmp, n);
    }
}
static void ctx_free(KFCtx *c) {
    if (!c) return;
    for (size_t i = 0; i < nslots; i++) if (slots[i].release) slots[i].release(c->bytes + slots[i].off);
    ev_saved_free(&c->units); (free)(c->bytes); (free)(c);
}

/* ---- stacks ---- */
KStack *kf_new(void) {
    KStack *ks = (calloc)(1, sizeof *ks); if (!ks) abort();
    ks->why = "";
    BUMP(stacks); __atomic_add_fetch(&S.live_stacks, 1, __ATOMIC_RELAXED);
    return ks;
}
static void stack_release(KStack *ks) {
    pages_free(ks->page); ks->page = NULL;
    ctx_free(ks->ctx); ks->ctx = NULL;
    __atomic_sub_fetch(&S.live_stacks, 1, __ATOMIC_RELAXED);
    (free)(ks);
}

/* the driver: steps from the top frame until the stack completes, a frame
 * suspends, or (between steps) the grant is spent */
static void run(KStack *ks) {
    while (ks->top) {
        if (kf_due(ks)) return;
        KF *f = ks->top;
        KStatus st = f->fam->step(ks, f);
        if (st == KS_DONE) { pop(ks, f); continue; }
        if (st == KS_CALL) continue;
        return;   /* KS_YIELD / KS_WAIT: the top frame resumes at its program counter */
    }
    ks->done = true;
}

size_t kf_grant(KStack *ks, size_t budget) {
    if (ks->done) return 0;
    require(!ks->sync, "kframe: a synchronous stack is not granted");
    ks->budget = budget ? budget : 1; ks->used = 0; ks->started = true; ks->lock_base = kf_lock_depth;
    BUMP(grants);
    KStack *prev_tl = kf_tl; kf_tl = ks;
    if (!ks->ctx) ks->ctx = ctx_new();
    ctx_swap(ks->ctx);                                   /* the computation's dynamic state is current on this thread */
    if (!ks->scoped) { reuse_tl_scope = ks->acct; ks->scoped = true; }   /* its accounting owner, from its first grant on (computation-local afterwards) */
    size_t ev_base = ev_depth();
    ev_begin(EK_KERNEL_GRANT, OCC(OCC_OP, ks->job), 0);  /* HANDOFF §6: the transitions of a grant are one primitive event */
    ev_attach(&ks->ctx->units);                          /* the units its steps left open continue */
    run(ks);
    require(kf_lock_depth == ks->lock_base, "kframe: a step returned holding a lock");
    if (!ks->done) { ev_detach(ev_base + 1, &ks->ctx->units); BUMP(suspends); }
    ev_unwind_to(ev_base);
    ctx_swap(ks->ctx);                                   /* this thread's own state again */
    kf_tl = prev_tl;
    ev_quiesce();
    if (ks->done && ks->outcome == KO_PENDING) ks->outcome = ks->ok ? KO_OK : KO_INVALID;
    return ks->used;
}
void kf_free(KStack *ks) {
    if (!ks) return;
    if (ks->started) while (!ks->done) kf_grant(ks, KF_UNBOUNDED);
    stack_release(ks);
}
void kf_cancel(KStack *ks) {
    if (!ks) return;
    if (!ks->started || ks->done) { kf_free(ks); return; }
    /* DROP: every frame, innermost first, releases what it owns at its phase; nothing of the program runs */
    size_t n = 0;
    if (ks->ctx) ctx_swap(ks->ctx);       /* the drops see the computation's own state (its checker frames, scope, units) */
    while (ks->top) { KF *f = ks->top; if (f->fam->drop) f->fam->drop(f); pop(ks, f); n++; }
    if (ks->ctx) ctx_swap(ks->ctx);
    __atomic_add_fetch(&S.dropped, n, __ATOMIC_RELAXED); BUMP(cancelled);
    ks->cancel = true;
    stack_release(ks);
}
size_t kf_inspect(const KStack *ks, KFVisit v, void *ctx) {
    size_t lvl = 0;
    for (const KF *f = ks->top; f; f = f->up, lvl++) if (v) v(ctx, lvl, f->fam->name, f->phase);
    return lvl;
}

/* ---- waits ---- */
void kf_wait_prepare(KStack *s, KStack *on, uint64_t on_job) {
    s->used++; xl_add(&s->steps, &s->steps_carry, 1);   /* the wait is one transition */
    s->blocked = true; s->blocked_on = on; s->blocked_job = on ? on_job : 0;
    BUMP(waits);
}
void kf_wait_resumed(KStack *s) { s->blocked = false; s->blocked_on = NULL; s->blocked_job = 0; }
void kf_wait_plain(pthread_cond_t *cv, pthread_mutex_t *mu) { pthread_cond_wait(cv, mu); }

/* ---- synchronous drivers ---- */
/* KF_REPORT: where an engine step drove a family synchronously at the driver's lock depth (the top frame), printed at exit */
static struct { const char *name; uint64_t n; } viol[256]; static size_t nviol; static pthread_mutex_t viol_mu = PTHREAD_MUTEX_INITIALIZER;
static void violation_report(void) { for (size_t i = 0; i < nviol; i++) fprintf(stderr, "kframe: %s: %llu\n", viol[i].name, (unsigned long long)viol[i].n); }
static void violation_note(const char *name) {
    (pthread_mutex_lock)(&viol_mu);
    static bool reg; if (!reg) { reg = true; atexit(violation_report); }
    size_t i = 0; while (i < nviol && strcmp(viol[i].name, name)) i++;
    if (i == nviol && nviol < 256) { size_t L = strlen(name) + 1; char *c = (malloc)(L); memcpy(c, name, L); viol[nviol].name = c; viol[nviol].n = 0; nviol++; }
    if (i < nviol) viol[i].n++;
    (pthread_mutex_unlock)(&viol_mu);
}
void kf_overrun_note(const KStack *s) {
    if (getenv("KF_OVERRUN_ABORT")) abort();
    if (!getenv("KF_REPORT")) return;
    char buf[96]; snprintf(buf, sizeof buf, "overrun %s counter=%d locks=%d", s->top ? s->top->fam->name : "-", kf_last_counter, kf_lock_depth - s->lock_base);
    violation_note(buf);
}
static __thread KStack *sync_free;      /* records reused by this thread */
static __thread KStack *sync_all;       /* every record this thread made (released at thread exit, including one left by an unwound computation) */
static pthread_key_t sync_key; static pthread_once_t sync_once = PTHREAD_ONCE_INIT;
static void sync_release(void *v) { KStack *ks = v; while (ks) { KStack *n = ks->sync_next_all; pages_free(ks->page); (free)(ks); ks = n; } }
static void sync_key_init(void) { pthread_key_create(&sync_key, sync_release); }
KStack *kf_sync_begin(void) {
    if (kf_tl && kf_locks_held() == 0) {   /* an engine step called a family synchronously where it could have suspended */
        BUMP(sync_in_step);
        if (getenv("KF_REPORT")) { char b[96]; snprintf(b, sizeof b, "synchronous family inside an engine step under %s", kf_tl->top ? kf_tl->top->fam->name : "-"); violation_note(b); }
        if (getenv("KF_STRICT")) { fprintf(stderr, "kframe: synchronous family call inside an engine step (top frame %s)\n", kf_tl->top ? kf_tl->top->fam->name : "-"); abort(); }
    }
    KStack *ks = sync_free;
    if (ks) sync_free = ks->sync_prev;
    else { ks = (calloc)(1, sizeof *ks); if (!ks) abort(); pthread_once(&sync_once, sync_key_init); ks->sync_next_all = sync_all; sync_all = ks; pthread_setspecific(sync_key, sync_all); }
    if (ks->top) { while (ks->top) pop(ks, ks->top); }   /* a record left mid-run by an unwound computation is reused empty */
    ks->sync = true; ks->budget = KF_UNBOUNDED; ks->done = false; ks->top = NULL; ks->depth = 0;
    BUMP(sync_runs);
    return ks;
}
void kf_sync_run(KStack *ks) {
    while (ks->top) {
        KF *f = ks->top;
        KStatus st = f->fam->step(ks, f);
        if (st == KS_DONE) pop(ks, f);
        else require(st == KS_CALL, "kframe: a synchronous stack suspended");
    }
    ks->done = true;
}
void kf_sync_end(KStack *ks) { ks->sync_prev = sync_free; sync_free = ks; }   /* its (empty) pages stay with the record; released at thread exit */

#ifdef KF_LOCK_AUDIT
#include "fine.h"
/* ---- the lock-section audit: per outermost acquisition site, the maximum
 * number of fine steps this thread took while holding it, and the maximum
 * distinct-site count; printed at exit (single-threaded runs give exact
 * per-thread attribution; fine counters are global, so run the audit with
 * CUBICAL_WORKERS=0) ---- */
typedef struct { const char *site; uint64_t max, calls, total; } AuditSite;
static AuditSite audit[512]; static size_t naudit; static pthread_mutex_t audit_mu = PTHREAD_MUTEX_INITIALIZER;
static __thread const char *cur_site; static __thread uint64_t cur_start;
static uint64_t fine_total(void) { return fine_tl_steps; }
void kf_audit_enter(const char *site) { cur_site = site; cur_start = fine_total(); }
static void audit_report(void) {
    fprintf(stderr, "lock-section audit: %zu sites (max fine steps under the outermost lock)\n", naudit);
    for (size_t pass = 0; pass < naudit; pass++) { size_t best = pass; for (size_t j = pass + 1; j < naudit; j++) if (audit[j].max > audit[best].max) best = j; AuditSite t = audit[pass]; audit[pass] = audit[best]; audit[best] = t; }
    for (size_t i = 0; i < naudit; i++) fprintf(stderr, "  %-28s max=%-8llu calls=%-10llu mean=%.2f\n", audit[i].site, (unsigned long long)audit[i].max, (unsigned long long)audit[i].calls, audit[i].calls ? (double)audit[i].total / audit[i].calls : 0.0);
}
void kf_audit_leave(void) {
    uint64_t d = fine_total() - cur_start; const char *site = cur_site; cur_site = NULL;
    (pthread_mutex_lock)(&audit_mu);
    static bool registered; if (!registered) { registered = true; atexit(audit_report); }
    size_t i = 0; while (i < naudit && audit[i].site != site) i++;
    if (i == naudit && naudit < 512) { audit[naudit].site = site; audit[naudit].max = 0; audit[naudit].calls = 0; audit[naudit].total = 0; naudit++; }
    if (i < naudit) { if (d > audit[i].max) audit[i].max = d; audit[i].calls++; audit[i].total += d; }
    (pthread_mutex_unlock)(&audit_mu);
}
#endif
