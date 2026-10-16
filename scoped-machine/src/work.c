/* work.c — identity-execution accounting and cost refinement (§§60–71 under §73).
 *
 * Organisation:
 *   1. the record table (one counted open-addressing table of word records;
 *      every probe, word comparison and copied word is a frame step)
 *   2. the operation handle and frame engine (§71.1)
 *   3. atoms, sets, formulas (§67.2, §68.1)
 *   4. demand graphs, closure and extraction (§60)
 *   5. specialization (§62), the resource algebra (§61), cost differences (§63)
 *   6. typed records, preparation, realization (§66–§68.3)
 *   7. proofs, certificates, the direct fragment, schemas (§69–§70)
 *   8. geodesic certificates (§64.3)
 *   9. the ledger
 *
 * All records are immutable word tuples [KIND, ...] interned in one table;
 * ids are dense and never reused. Mutable side data (cached support/Must,
 * memo values, per-kind structs) lives in a parallel chunked array.
 */
#include "work.h"
#include "proof.h"
#include "scope.h"
#include "net.h"
#include "reuse.h"
#include <pthread.h>
#include <limits.h>

/* ---------------------------------------------------------------- 1. records ---- */

enum { K_ATOM = 1, K_SET, K_FORMULA, K_EXPR, K_BOUNDARY, K_PLAN, K_CONNECTOR, K_MODEL, K_PROBLEM, K_REAL, K_PROOF, K_CERT,
       K_FAMILY, K_SCHEMA, K_GEO, K_DGRAPH, K_DEMAND, K_WORKSET, K_COSTDIFF, K_LIST, K_AMAP, K_MEMO, K_MARK, K_WEIGHT, K_REDUCTION, K_JOB };

typedef struct {            /* per-record side data */
    SetId support, must;    /* cached formula facts (0 = not computed) */
    uint64_t val; bool has_val;   /* memo / mark value */
    void *ptr;              /* kind-specific struct, freed by its kind at teardown */
    uint8_t kind;
} Side;

#define CHUNK_WORDS 32          /* §81.2: the fixed chunk of a copy / relocation / release frame */
typedef struct {
    Words store;            /* [hash, n, w0..w_{n-1}] per record at off[id-1] */
    VEC(size_t) off;
    uint64_t *slots; size_t nslots, n;
    uint64_t *old; size_t old_n, cursor;   /* an incremental relocation in progress (framed growth) */
    uint64_t moving; size_t probe;          /* §94.2(4): the old slot being placed and its probe cursor */
    uint64_t gen;                           /* R1: slot-array generation; a saved probe cursor is valid only for its generation */
} KTab;

static struct {
    KTab tab;
    Chunked side;
    WorkLedger L; Phase phase;
    Chunked ops; size_t nops;    /* handles */
    FormulaId ZERO, ONE; SetId EMPTY; FamilyId FAM0, FAM1;
    VEC(void *) owned;      /* kind-specific structs to free */
    pthread_mutex_t mu;
    uint64_t mark_seq;
    bool live;
} W;

static uint64_t hash_step(uint64_t h, uint64_t w) { h ^= w + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); return h * 0xBF58476D1CE4E5B9ULL; }

static void ktab_init(KTab *t) { words_init(&t->store); t->off.data = NULL; t->off.len = t->off.cap = 0; t->nslots = 1024; t->slots = calloc(t->nslots, sizeof(uint64_t)); require(t->slots, "out of memory"); t->n = 0; }
static void ktab_free(KTab *t) { words_free(&t->store); vec_free(&t->off); free(t->slots); free(t->old); }
static const uint64_t *rec_words(uint64_t id, size_t *n) { size_t o = W.tab.off.data[id - 1]; *n = (size_t)W.tab.store.w[o + 1]; return W.tab.store.w + o + 2; }
static uint64_t rec_hash(uint64_t id) { return W.tab.store.w[W.tab.off.data[id - 1]]; }
static Side *side(uint64_t id) { return (Side *)chunked_at(&W.side, id - 1); }
static uint8_t rec_kind(uint64_t id) { size_t n; return (uint8_t)rec_words(id, &n)[0]; }
static uint64_t rec_w(uint64_t id, size_t i) { size_t n; const uint64_t *w = rec_words(id, &n); require(i < n, "record field"); return w[i]; }

/* synchronous interning, charged per hashed word, probe and compared word
 * (used by constructors that are not themselves framed operations; the
 * framed INTERN below performs the same steps one per frame) */
static void charge(FrameFamily f) { W.L.frames[f]++; W.L.by_phase[W.phase]++; }
/* §94.2(6): the reuse administration a kernel call performs (shape nodes
 * built, dependency checks, receipt instances) is charged into its ledger
 * families from the kernel's own counters around the call; these are
 * accounted, not resumable (see the bounded-helper table) */
typedef struct { uint64_t shape, dep, rc; } KernelMark;
static KernelMark kernel_mark(void) { KernelMark m = { reuse_count(REUSE_SHAPE_NODE), reuse_count(REUSE_DEPENDENCY_CHECK), reuse_count(REUSE_RECEIPT_INSTANCE) }; return m; }
static void kernel_charge(KernelMark m) {
    uint64_t a = reuse_count(REUSE_SHAPE_NODE) - m.shape, b = reuse_count(REUSE_DEPENDENCY_CHECK) - m.dep, c = reuse_count(REUSE_RECEIPT_INSTANCE) - m.rc;
    W.L.frames[FR_SHAPE_NODE] += a; W.L.frames[FR_DEPENDENCY_CHECK] += b; W.L.frames[FR_RECEIPT] += c; W.L.by_phase[W.phase] += a + b + c;
    W.L.kernel_calls++;
}
/* growth: a new slot array is allocated and the old one relocated in chunks
 * of CHUNK_WORDS slots; a framed INTERN performs one chunk per frame, every
 * other probe path first completes a pending relocation (counted) */
static void ktab_begin_grow(void) {
    KTab *t = &W.tab;
    size_t ns = t->nslots * 2; uint64_t *sl = calloc(ns, sizeof(uint64_t)); require(sl, "out of memory");
    t->old = t->slots; t->old_n = t->nslots; t->cursor = 0; t->gen++;
    t->slots = sl; t->nslots = ns; W.L.alloc_words += ns; charge(FR_ALLOCATE_CHUNK);
}
/* one relocation unit: at most CHUNK_WORDS source-slot visits plus probes in
 * total (a collision chain in progress is resumed from its probe cursor);
 * true when the relocation is complete */
static bool ktab_grow_chunk(void) {
    KTab *t = &W.tab;
    if (!t->old) return true;
    size_t budget = CHUNK_WORDS;
    while (budget) {
        if (!t->moving) {
            if (t->cursor >= t->old_n) break;
            uint64_t id = t->old[t->cursor++]; budget--;
            if (!id) continue;
            t->moving = id; t->probe = rec_hash(id) & (t->nslots - 1);
            continue;
        }
        W.L.probes++; budget--;
        if (t->slots[t->probe]) { t->probe = (t->probe + 1) & (t->nslots - 1); continue; }
        t->slots[t->probe] = t->moving; t->moving = 0;
    }
    charge(FR_TABLE_PROBE);
    if (t->cursor >= t->old_n && !t->moving) { free(t->old); t->old = NULL; W.L.release_words += t->old_n; charge(FR_RELEASE_CHUNK); return true; }
    return false;
}
static void ktab_settle(void) { while (!ktab_grow_chunk()) ; }
static void ktab_grow(void) { ktab_settle(); ktab_begin_grow(); ktab_settle(); }
static uint64_t intern_sync(const uint64_t *w, size_t n, bool *created) {
    KTab *t = &W.tab;
    ktab_settle();
    if (created) *created = false;
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ n;
    for (size_t i = 0; i < n; i++) { h = hash_step(h, w[i]); W.L.limb_ops++; charge(FR_FORMULA_INTERN_STEP); }
    if ((t->n + 1) * 2 > t->nslots) ktab_grow();
    size_t j = h & (t->nslots - 1);
    for (;;) {
        W.L.probes++; charge(FR_TABLE_PROBE);
        uint64_t id = t->slots[j];
        if (!id) break;
        if (rec_hash(id) == h) {
            size_t m; const uint64_t *v = rec_words(id, &m);
            bool eq = m == n; for (size_t i = 0; eq && i < n; i++) { W.L.word_compares++; charge(FR_FORMULA_INTERN_STEP); eq = v[i] == w[i]; }
            if (eq) return id;
        }
        j = (j + 1) & (t->nslots - 1);
    }
    size_t off = t->store.n;
    words_push(&t->store, h); words_push(&t->store, n);
    for (size_t i = 0; i < n; i++) { words_push(&t->store, w[i]); W.L.alloc_words++; charge(FR_ALLOCATE_CHUNK); }
    vec_push(&t->off, off); t->n++;
    uint64_t id = t->n; t->slots[j] = id;
    Side *s = side(id); memset(s, 0, sizeof *s); s->kind = (uint8_t)w[0];
    if (created) *created = true;
    return id;
}
/* a fixed-key lookup (≤ 4-word keys): never drains a relocation another
 * operation began — during one, a record not yet moved is still found in the
 * old slot array; probes are counted (R6: a collision chain is walked inside
 * the caller's unit; disclosed in the bounded-helper table) */
static uint64_t find_in(const uint64_t *slots, size_t nslots, uint64_t h, const uint64_t *w, size_t n) {
    size_t j = h & (nslots - 1);
    for (;;) {
        W.L.probes++; charge(FR_TABLE_PROBE);
        uint64_t id = slots[j];
        if (!id) return 0;
        if (rec_hash(id) == h) {
            size_t m; const uint64_t *v = rec_words(id, &m);
            bool eq = m == n; for (size_t i = 0; eq && i < n; i++) { W.L.word_compares++; charge(FR_FORMULA_INTERN_STEP); eq = v[i] == w[i]; }
            if (eq) return id;
        }
        j = (j + 1) & (nslots - 1);
    }
}
static uint64_t find_sync(const uint64_t *w, size_t n) {
    KTab *t = &W.tab;
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ n;
    for (size_t i = 0; i < n; i++) { h = hash_step(h, w[i]); W.L.limb_ops++; charge(FR_FORMULA_INTERN_STEP); }
    uint64_t id = find_in(t->slots, t->nslots, h, w, n);
    if (!id && t->old) id = find_in(t->old, t->old_n, h, w, n);
    return id;
}
static void *own(void *p) { vec_push(&W.owned, p); return p; }

/* ---------------------------------------------------------------- 2. frames ---- */
typedef struct DGraph DGraph; typedef struct Geo Geo;
static uint64_t dgraph_rev(const DGraph *g); static uint64_t geo_rev(const Geo *g);

enum {   /* operation families (frame kinds) */
    OF_INTERN = 1, OF_LOOKUP, OF_MKF, OF_RESTRICT, OF_SUPPORT, OF_MUST, OF_SUBST, OF_SUM, OF_SETOP, OF_DEMAND, OF_EXTRACT,
    OF_SPEC_SET, OF_SPEC_FORMULA, OF_PREPARE, OF_EXPRF, OF_REALIZE, OF_REALVISIT, OF_CHECKCERT, OF_PROOF, OF_REDUCE, OF_ANTICHAIN,
    OF_FAMOP, OF_NORMALIZE, OF_SUBSET, OF_GEO, OF_MAPF, OF_MAPP, OF_MAPSET, OF_ATOMSPEC, OF_LIST, OF_SORT,
    OF_JOIN   /* §94.2(4): the bounded request of a shared operation — key interning, then join/create/deliver */
};
enum { SO_UNION = 1, SO_INTER, SO_DIFF };

typedef struct {
    uint16_t fam, ph;
    uint64_t a, b, c, d, e;      /* operands */
    uint64_t i, j;               /* component indices */
    uint64_t acc, acc2, acc3, acc4;
    Words buf, buf2, buf3;       /* owned variable data */
} Frame;

/* §75: a Job is a persistent producer of one pure operation, keyed by its
 * family and immutable operands (plus the external versions the operation
 * actually depends on). Its frame stack is the shared continuation; private
 * helper frames (interning, lookups, lists, sorts, visits with pointers) run
 * on the same stack, while a request for another keyed operation joins or
 * creates that operation's own job and suspends this one (waiting_on). A
 * handle is one consumer of a root job: stepping a handle services enabled
 * jobs in the root's dependency cone, one frame per unit of budget; two
 * handles of one key step the same job and never execute two copies of it.
 * Releasing a handle leaves the job and every READY answer in the store. */
typedef struct {
    uint64_t id;                 /* its key record id (also the mark namespace) */
    OpStatus st; const char *diag;
    uint64_t result, ret;
    VEC(Frame) stack;
    Phase phase; int family;
    uint64_t waiting_on;         /* job id this job is suspended on, 0 when enabled */
    VEC(uint64_t) waiters;       /* jobs suspended on this job (one registration per join; delivered one per unit) */
    uint64_t frames;
    /* §94.2(2–3): the cone path of this job when it is driven as a root:
     * the chain root → … → tip, extended or popped one hop per unit */
    VEC(uint64_t) path;
} Op;                            /* historical name: the job record */
typedef struct { uint64_t job; uint64_t frames; bool released; } Handle;

#define RULES_VERSION 1          /* the fixed proof-rule / direct-reduction rule set of this build */
static void frame_free(Frame *f);
static Op *JOB(uint64_t id) { Op *o = (Op *)side(id)->ptr; require(o && side(id)->kind == K_JOB, "not a job"); return o; }
static Handle *HND(OpId h) { require(h && h <= W.nops, "unknown operation handle"); return (Handle *)chunked_get(&W.ops, h - 1); }
static bool shared_family(uint16_t fam) {
    switch (fam) { case OF_INTERN: case OF_LOOKUP: case OF_LIST: case OF_NORMALIZE: case OF_REALVISIT: case OF_SORT: return false; default: return true; }
}
/* the persistent key of a shared frame: family, operands, and the external
 * versions the operation reads (§75.1) */
static size_t job_key(const Frame *f, uint64_t *w) {
    size_t n = 0; w[n++] = K_JOB; w[n++] = f->fam; w[n++] = f->a; w[n++] = f->b; w[n++] = f->c; w[n++] = f->d;
    switch (f->fam) {
    case OF_PROOF: case OF_REDUCE: w[n++] = RULES_VERSION; break;
    case OF_SPEC_SET: case OF_SPEC_FORMULA: case OF_ATOMSPEC: w[n++] = global_env_version(); break;
    case OF_PREPARE: case OF_CHECKCERT: w[n++] = check_session_id(); w[n++] = global_env_version(); break;
    case OF_GEO: w[n++] = geo_rev((Geo *)side(f->a)->ptr); break;
    case OF_DEMAND: w[n++] = dgraph_rev((DGraph *)side(f->a)->ptr); break;
    default: break;
    }
    return n;
}
static Phase phase_of_family(uint16_t fam) {
    switch (fam) {
    case OF_PREPARE: case OF_EXPRF: case OF_DEMAND: case OF_EXTRACT: case OF_SPEC_SET: case OF_SPEC_FORMULA: case OF_ATOMSPEC: case OF_MAPF: case OF_MAPP: case OF_MAPSET: return PH_PREPARE;
    case OF_CHECKCERT: case OF_PROOF: case OF_GEO: return PH_CHECK;
    case OF_REALIZE: return PH_COMMIT;
    default: return PH_REWRITE;
    }
}
/* find or create the job of a shared frame; *created tells whether its stack was just started */
static Op *job_for(Frame f, bool *created) {
    uint64_t w[10]; size_t n = job_key(&f, w);
    if (!shared_family(f.fam)) { w[1] = f.fam; w[2] = ++W.mark_seq; n = 3; }   /* a private root (buffer-carrying) is never shared */
    bool fresh; uint64_t id = intern_sync(w, n, &fresh);
    W.L.probes++; W.L.memo_lookup++; charge(FR_PRODUCER_LOOKUP);
    Side *sd = side(id);
    if (sd->ptr && ((Op *)sd->ptr)->st == OP_COMPLETE) W.L.memo_hit++;
    if (!sd->ptr) {
        Op *o = own(calloc(1, sizeof *o)); require(o, "out of memory");
        o->id = id; o->st = OP_RUNNING; o->phase = phase_of_family(f.fam); o->family = f.fam;
        vec_push(&o->stack, f);
        sd->ptr = o; sd->kind = K_JOB;
        *created = true;
        return o;
    }
    frame_free(&f);
    *created = false;
    return (Op *)sd->ptr;
}
static Frame fr(uint16_t fam, uint64_t a, uint64_t b, uint64_t c, uint64_t d) { Frame f; memset(&f, 0, sizeof f); f.fam = fam; f.a = a; f.b = b; f.c = c; f.d = d; words_init(&f.buf); words_init(&f.buf2); words_init(&f.buf3); return f; }
static void frame_free(Frame *f) {
    size_t n = f->buf.n + f->buf2.n;
    W.L.release_words += n; if (n) charge(FR_RELEASE_CHUNK);
    words_free(&f->buf); words_free(&f->buf2); words_free(&f->buf3);
}
static Frame *top(Op *o) { return &o->stack.data[o->stack.len - 1]; }
static void fail(Op *o, const char *why);
static void limit(Op *o, const char *why);
static void push_intern(Op *o, const uint64_t *w, size_t n);
/* request a frame: a private helper is pushed on this job's stack; a shared
 * operation is requested through a JOIN frame (§94.2(4)): its key is
 * interned by the framed INTERN (one hash word / probe / compared word per
 * unit), then the job is found or created — READY delivers at once, RUNNING
 * joins through a suspended cycle check, ABSENT starts the job. The shared
 * frame's operands travel in the JOIN frame (shared frames carry no
 * buffers; a private root never passes through here). */
static void push(Op *o, Frame f) {
    if (!shared_family(f.fam)) { vec_push(&o->stack, f); return; }
    require(f.buf.n == 0 && f.buf2.n == 0 && f.buf3.n == 0, "a shared frame carries no buffer");
    Frame j = fr(OF_JOIN, f.a, f.b, f.c, f.d); j.acc = f.fam; j.e = f.e;
    uint64_t w[10]; size_t n = job_key(&f, w); words_append(&j.buf, w, n);
    frame_free(&f);
    vec_push(&o->stack, j);
}
/* the job record of a key (created when absent, with the requested frame) */
static Op *job_at(uint64_t id, const Frame *f, bool *created) {
    Side *sd = side(id);
    *created = false;
    if (sd->ptr && ((Op *)sd->ptr)->st == OP_COMPLETE) W.L.memo_hit++;
    if (!sd->ptr) {
        Op *o = own(calloc(1, sizeof *o)); require(o, "out of memory");
        o->id = id; o->st = OP_RUNNING; o->phase = phase_of_family(f->fam); o->family = f->fam;
        vec_push(&o->stack, *f);
        sd->ptr = o; sd->kind = K_JOB;
        *created = true;
    }
    return (Op *)sd->ptr;
}
/* one delivery: the finished job j answers waiter w (one unit, charged) */
static void deliver_to(Op *w, Op *j) {
    w->waiting_on = 0;
    if (j->st == OP_COMPLETE) { w->ret = j->result; W.L.memo_deliver++; charge(FR_ALIAS_DELIVERY); reuse_bump(REUSE_READY_HIT); }
    else if (j->st == OP_INVALID) fail(w, j->diag);
    else limit(w, j->diag);
}
static void step_join(Op *o, Frame *f) {
    switch (f->ph) {
    case 0: f->ph = 1; push_intern(o, f->buf.w, f->buf.n); return;
    case 1: {
        Frame g = fr((uint16_t)f->acc, f->a, f->b, f->c, f->d); g.e = f->e;
        bool created; Op *j = job_at(o->ret, &g, &created);
        if (!created) frame_free(&g);
        W.L.memo_lookup++;
        if (j == o) { fail(o, "cyclic request: an operation requested itself"); return; }
        if (j->st != OP_RUNNING) { frame_free(f); o->stack.len--; deliver_to(o, j); return; }
        if (created) { frame_free(f); o->stack.len--; o->waiting_on = j->id; vec_push(&j->waiters, o->id); return; }
        /* join a running job: the cycle check walks j's chain one hop per
         * unit before the wait is committed (§94.2(3)) */
        reuse_bump(REUSE_RUNNING_JOIN);
        f->ph = 2; f->acc2 = j->id; f->acc3 = j->id; return;
    }
    case 2: {   /* one hop of the cycle check */
        charge(FR_CYCLE_CHECK);
        Op *j = JOB(f->acc2);
        if (j->st != OP_RUNNING) { frame_free(f); o->stack.len--; deliver_to(o, j); return; }
        Op *c = JOB(f->acc3);
        uint64_t next = c->st == OP_RUNNING ? c->waiting_on : 0;
        if (next == o->id) { fail(o, "cyclic request among running operations"); return; }
        if (next) { f->acc3 = next; return; }
        frame_free(f); o->stack.len--; o->waiting_on = j->id; vec_push(&j->waiters, o->id); return;
    }
    }
}
static void stack_drop(Op *o) { for (size_t i = 0; i < o->stack.len; i++) frame_free(&o->stack.data[i]); vec_free(&o->stack); }
static void fin(Op *o, uint64_t v) { Frame *t = top(o); frame_free(t); o->stack.len--; o->ret = v; if (!o->stack.len) { o->st = OP_COMPLETE; o->result = v; stack_drop(o); } }
static void fail(Op *o, const char *why) { if (o->st != OP_RUNNING) return; o->st = OP_INVALID; o->diag = why; }   /* retained frames are released one per unit by the scheduler (§94.2(5)) */
static void limit(Op *o, const char *why) { if (o->st != OP_RUNNING) return; o->st = OP_RESOURCE_LIMIT; o->diag = why; }   /* state retained, not resumable */

/* checked natural arithmetic: one limb operation */
static bool add_checked(Cost a, Cost b, Cost *out) {
    W.L.limb_ops++;
    if (a == COST_INF || b == COST_INF) { *out = COST_INF; return true; }
    if (a >= COST_MAX - b) return false;
    *out = a + b; return true;
}
Cost cost_add(Cost a, Cost b, bool *overflow) { Cost r; bool ok = add_checked(a, b, &r); if (overflow) *overflow = !ok; return ok ? r : COST_MAX; }

/* ---- the frame bodies ---- */
static void step_intern(Op *o, Frame *f);
static void step_lookup(Op *o, Frame *f);
static void step_mkf(Op *o, Frame *f);
static void step_restrict(Op *o, Frame *f);
static void step_support(Op *o, Frame *f);
static void step_subst(Op *o, Frame *f);
static void step_sum(Op *o, Frame *f);
static void step_setop(Op *o, Frame *f);
static void step_subset(Op *o, Frame *f);
static void step_demand(Op *o, Frame *f);
static void step_extract(Op *o, Frame *f);
static void step_spec_set(Op *o, Frame *f);
static void step_atomspec(Op *o, Frame *f);
static void step_spec_formula(Op *o, Frame *f);
static void step_prepare(Op *o, Frame *f);
static void step_exprf(Op *o, Frame *f);
static void step_realize(Op *o, Frame *f);
static void step_realvisit(Op *o, Frame *f);
static void step_checkcert(Op *o, Frame *f);
static void step_proof(Op *o, Frame *f);
static void step_reduce(Op *o, Frame *f);
static void step_antichain(Op *o, Frame *f);
static void step_famop(Op *o, Frame *f);
static void step_normalize(Op *o, Frame *f);
static void step_geo(Op *o, Frame *f);
static void step_mapf(Op *o, Frame *f);
static void step_mapp(Op *o, Frame *f);
static void step_mapset(Op *o, Frame *f);
static void step_list(Op *o, Frame *f);
static void step_sort(Op *o, Frame *f);
static void step_join(Op *o, Frame *f);
static void push_intern(Op *o, const uint64_t *w, size_t n);

static FrameFamily family_of(const Frame *f) {
    switch (f->fam) {
    case OF_INTERN: return (f->ph == 3 || f->ph == 5) ? FR_ALLOCATE_CHUNK : f->ph == 0 ? FR_FORMULA_INTERN_STEP : FR_TABLE_PROBE;   /* ph 4: relocation unit */
    case OF_LOOKUP: return f->ph == 0 ? FR_FORMULA_INTERN_STEP : FR_TABLE_PROBE;
    case OF_JOIN: return f->ph == 0 ? FR_PRODUCER_LOOKUP : FR_SCHEDULE_STEP;
    case OF_MKF: case OF_EXPRF: case OF_MAPF: case OF_SPEC_FORMULA: return FR_FORMULA_VISIT;
    case OF_RESTRICT: return f->ph == 4 ? FR_COFACTOR_REBUILD : FR_COFACTOR_VISIT;
    case OF_SUBST: return FR_COFACTOR_VISIT;
    case OF_SUPPORT: return FR_SUPPORT_CHUNK;
    case OF_MUST: return FR_MUST_CHUNK;
    case OF_SUM: return FR_COST_ADD_CHUNK;
    case OF_SETOP: case OF_SUBSET: case OF_LIST: case OF_MAPSET: case OF_SORT: return FR_SUPPORT_CHUNK;
    case OF_DEMAND: case OF_EXTRACT: return FR_DEMAND_VISIT;
    case OF_SPEC_SET: case OF_ATOMSPEC: return FR_SPECIALIZE_VISIT;
    case OF_PREPARE: return f->ph == 1 ? FR_VALIDATE_PREPARED_BOUNDARY : FR_PREPARE_VISIT;
    case OF_REALIZE: case OF_REALVISIT: return FR_REALIZATION_VISIT;
    case OF_CHECKCERT: case OF_PROOF: case OF_MAPP: return FR_CERTIFICATE_VISIT;
    case OF_REDUCE: return FR_COST_COMPARE_CHUNK;
    case OF_ANTICHAIN: case OF_FAMOP: case OF_NORMALIZE: return FR_FAMILY_CHUNK;
    case OF_GEO: return FR_GEODESIC_VISIT;
    default: return FR_PREPARE_VISIT;
    }
}

static void step(Op *o) {
    Frame *f = top(o);
    charge(family_of(f));
    switch (f->fam) {
    case OF_INTERN: step_intern(o, f); break;
    case OF_LOOKUP: step_lookup(o, f); break;
    case OF_MKF: step_mkf(o, f); break;
    case OF_RESTRICT: step_restrict(o, f); break;
    case OF_SUPPORT: case OF_MUST: step_support(o, f); break;
    case OF_SUBST: step_subst(o, f); break;
    case OF_SUM: step_sum(o, f); break;
    case OF_SETOP: step_setop(o, f); break;
    case OF_SUBSET: step_subset(o, f); break;
    case OF_DEMAND: step_demand(o, f); break;
    case OF_EXTRACT: step_extract(o, f); break;
    case OF_SPEC_SET: step_spec_set(o, f); break;
    case OF_ATOMSPEC: step_atomspec(o, f); break;
    case OF_SPEC_FORMULA: step_spec_formula(o, f); break;
    case OF_PREPARE: step_prepare(o, f); break;
    case OF_EXPRF: step_exprf(o, f); break;
    case OF_REALIZE: step_realize(o, f); break;
    case OF_REALVISIT: step_realvisit(o, f); break;
    case OF_CHECKCERT: step_checkcert(o, f); break;
    case OF_PROOF: step_proof(o, f); break;
    case OF_REDUCE: step_reduce(o, f); break;
    case OF_ANTICHAIN: step_antichain(o, f); break;
    case OF_FAMOP: step_famop(o, f); break;
    case OF_NORMALIZE: step_normalize(o, f); break;
    case OF_GEO: step_geo(o, f); break;
    case OF_MAPF: step_mapf(o, f); break;
    case OF_MAPP: step_mapp(o, f); break;
    case OF_MAPSET: step_mapset(o, f); break;
    case OF_LIST: step_list(o, f); break;
    case OF_SORT: step_sort(o, f); break;
    case OF_JOIN: step_join(o, f); break;
    default: die("unknown frame family %u", f->fam);
    }
}

/* one unit of service in the cone of root (§94.2(2–3)): the root keeps the
 * path root → … → tip of its waiting chain; a unit either extends the path
 * by one hop, pops a finished tip and delivers its answer to the waiter
 * below it, releases one retained frame of a failed tip, or steps the tip's
 * top frame. No unit traverses a chain or delivers to more than one waiter.
 * false when nothing in the cone is enabled (the root is finished, or waits
 * on a running job of another cone — a cyclic wait cannot arise: joins are
 * committed only after their chain check). */
static Op *tip_of(Op *root) { return root->path.len ? JOB(root->path.data[root->path.len - 1]) : root; }
static bool service(Op *root) {
    Op *t = tip_of(root);
    Phase saved = W.phase; W.phase = root->phase;   /* charged to the requesting root's phase */
    bool progressed = true;
    if (t->st != OP_RUNNING) {
        if (t->stack.len) { frame_free(top(t)); t->stack.len--; if (!t->stack.len) vec_free(&t->stack); charge(FR_RELEASE_CHUNK); }   /* retained frames of a failed job, one per unit */
        else if (!root->path.len) progressed = false;                   /* the root itself is finished */
        else { root->path.len--; Op *w = tip_of(root); if (w->waiting_on == t->id) deliver_to(w, t); else charge(FR_SCHEDULE_STEP); }
    } else if (t->waiting_on) {
        Op *n = JOB(t->waiting_on);
        if (n->st != OP_RUNNING) deliver_to(t, n);
        else { vec_push(&root->path, n->id); charge(FR_SCHEDULE_STEP); }
    } else step(t);
    W.phase = saved;
    return progressed;
}
static OpId handle_new(Frame f) {
    bool created; Op *j = job_for(f, &created);
    Handle *h = (Handle *)chunked_at(&W.ops, W.nops); memset(h, 0, sizeof *h); h->job = j->id; W.nops++;
    return W.nops;
}
static OpId op_new(int family, Phase ph, Frame f) { (void)family; (void)ph; return handle_new(f); }
OpStatus op_step(OpId h, size_t budget) {
    pthread_mutex_lock(&W.mu);
    Handle *hd = HND(h); Op *root = JOB(hd->job);
    while (root->st == OP_RUNNING && budget) { if (!service(root)) break; budget--; hd->frames++; }
    OpStatus s = root->st;
    pthread_mutex_unlock(&W.mu);
    return s;
}
OpStatus op_status(OpId h) { pthread_mutex_lock(&W.mu); OpStatus s = JOB(HND(h)->job)->st; pthread_mutex_unlock(&W.mu); return s; }
uint64_t op_result(OpId h) { pthread_mutex_lock(&W.mu); Op *o = JOB(HND(h)->job); require(o->st == OP_COMPLETE, "result of an operation that has not completed"); uint64_t r = o->result; pthread_mutex_unlock(&W.mu); return r; }
const char *op_diagnostic(OpId h) { pthread_mutex_lock(&W.mu); const char *d = JOB(HND(h)->job)->diag; pthread_mutex_unlock(&W.mu); return d; }
uint64_t op_frames(OpId h) { pthread_mutex_lock(&W.mu); uint64_t n = HND(h)->frames; pthread_mutex_unlock(&W.mu); return n; }
/* §75.2: releasing a handle retires only the handle; the job, its
 * continuation and its answer stay for every other consumer and the store */
void op_release(OpId h) { pthread_mutex_lock(&W.mu); Handle *hd = HND(h); hd->released = true; charge(FR_RELEASE_CHUNK); pthread_mutex_unlock(&W.mu); }
/* drive a job's cone to a non-running state under the lock; returns the result, or 0 with *why */
static uint64_t run_locked(Op *o, const char **why) {
    while (o->st == OP_RUNNING) if (!service(o)) break;
    if (o->st != OP_COMPLETE) { if (why) *why = o->st == OP_RUNNING ? "operation suspended: no enabled job (cyclic wait)" : o->diag; return 0; }
    return o->result;
}
/* the synchronous entry of a shared operation: find or start its job
 * (counting the lookup and, for a completed answer, its delivery) */
static Op *job_sync(Frame f) {
    bool created; Op *j = job_for(f, &created);
    if (!created && j->st == OP_COMPLETE) { W.L.memo_deliver++; charge(FR_ALIAS_DELIVERY); reuse_bump(REUSE_READY_HIT); }
    return j;
}
static uint64_t run_op(int family, Phase ph, Frame f, const char **why) { (void)family; (void)ph; return run_locked(job_sync(f), why); }
#define LOCK pthread_mutex_lock(&W.mu)
#define UNLOCK pthread_mutex_unlock(&W.mu)

/* INTERN: a = unused, buf = the key words.  ph0 HASH(i) → ph1 PROBE → ph2 COMPARE(j) → ph3 COPY(i) → done.
 * Growth is performed synchronously-counted when the load bound is reached
 * (every moved slot is a counted probe). */
/* INTERN (R1, §94.2(4)): a suspended insertion is one transaction.
 *   ph0 HASH one word per unit;
 *   ph4 one relocation unit of a growth in progress (then re-probe from the hash);
 *   ph1 PROBE one slot per unit — a saved cursor is valid only for the slot
 *       array's generation (e), otherwise the probe restarts from the hash;
 *   ph2 COMPARE one word per unit against a candidate equal-hash record;
 *   ph5 RESERVE: the record's whole extent (header + payload) is reserved in
 *       the store in one unit, so no other candidate can interleave its words;
 *       the record stays unpublished (no id, no slot) until complete;
 *   ph3 COPY one word per unit into the reserved extent;
 *   then back to ph1 with the candidate held (acc4): the probe is
 *   re-established in the current table; an equal key interned meanwhile is
 *   returned as the canonical id (the reserved extent is abandoned, counted
 *   as released), otherwise the complete record is published at the slot the
 *   fresh probe found. */
static void step_intern(Op *o, Frame *f) {
    KTab *t = &W.tab;
    switch (f->ph) {
    case 0:
        if (f->i == 0) f->acc = 0x9E3779B97F4A7C15ULL ^ f->buf.n;
        if (f->i < f->buf.n) { f->acc = hash_step(f->acc, f->buf.w[f->i]); f->i++; W.L.limb_ops++; return; }
        if (t->old || (t->n + 1) * 2 > t->nslots) { if (!t->old) ktab_begin_grow(); f->ph = 4; return; }
        f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; return;
    case 4:   /* one relocation unit */
        if (ktab_grow_chunk()) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; }
        return;
    case 1: {   /* one probe */
        if (t->old) { f->ph = 4; return; }
        if (f->e != t->gen) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; }   /* the table changed since this cursor was taken */
        W.L.probes++;
        uint64_t id = t->slots[f->j];
        if (!id) {
            if (!f->acc4) { f->ph = 5; return; }                                 /* no candidate yet: reserve */
            /* publish the complete candidate at this slot */
            vec_push(&t->off, (size_t)f->acc2); t->n++;
            uint64_t nid = t->n; t->slots[f->j] = nid;
            Side *sd = side(nid); memset(sd, 0, sizeof *sd); sd->kind = (uint8_t)f->buf.w[0];
            o->ret = 0; fin(o, nid); o->ret = nid; return;
        }
        if (rec_hash(id) == f->acc) { size_t m; rec_words(id, &m); if (m == f->buf.n) { f->acc3 = id; f->i = 0; f->ph = 2; return; } }
        f->j = (f->j + 1) & (t->nslots - 1); return;
    }
    case 2: {   /* compare one word */
        if (t->old || f->e != t->gen) { f->ph = 1; return; }                     /* re-probe: the table moved under the comparison */
        size_t m; const uint64_t *v = rec_words(f->acc3, &m);
        W.L.word_compares++;
        if (f->i < m) { if (v[f->i] != f->buf.w[f->i]) { f->j = (f->j + 1) & (t->nslots - 1); f->ph = 1; return; } f->i++; return; }
        if (f->acc4) { W.L.release_words += f->buf.n + 2; charge(FR_RELEASE_CHUNK); }   /* an equal key was interned meanwhile: the candidate is abandoned */
        fin(o, f->acc3); return;
    }
    case 5: {   /* reserve the record's extent: header now, payload words zero until copied */
        f->acc2 = t->store.n;
        words_push(&t->store, f->acc); words_push(&t->store, f->buf.n);
        for (size_t k = 0; k < f->buf.n; k++) words_push(&t->store, 0);          /* one allocation unit for the extent (amortized growth, charged) */
        W.L.alloc_words += f->buf.n + 2; charge(FR_ALLOCATE_CHUNK);
        f->i = 0; f->ph = 3; return;
    }
    case 3: {   /* copy one word into the reserved extent; then re-probe with the candidate held */
        if (f->i < f->buf.n) { t->store.w[f->acc2 + 2 + f->i] = f->buf.w[f->i]; f->i++; return; }
        f->acc4 = 1; f->ph = 1; return;
    }
    }
}
/* LOOKUP: same without insertion; result 0 when absent */
static void step_lookup(Op *o, Frame *f) {
    KTab *t = &W.tab;
    switch (f->ph) {
    case 0:
        if (f->i == 0) f->acc = 0x9E3779B97F4A7C15ULL ^ f->buf.n;
        if (f->i < f->buf.n) { f->acc = hash_step(f->acc, f->buf.w[f->i]); f->i++; W.L.limb_ops++; return; }
        f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; return;
    case 3:   /* one relocation unit of a growth in progress, then re-probe */
        if (ktab_grow_chunk()) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; }
        return;
    case 1: {
        if (t->old) { f->ph = 3; return; }
        if (f->e != t->gen) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; }
        W.L.probes++;
        uint64_t id = t->slots[f->j];
        if (!id) { fin(o, 0); return; }
        if (rec_hash(id) == f->acc) { size_t m; rec_words(id, &m); if (m == f->buf.n) { f->acc3 = id; f->i = 0; f->ph = 2; return; } }
        f->j = (f->j + 1) & (t->nslots - 1); return;
    }
    case 2: {
        if (t->old || f->e != t->gen) { f->ph = 1; return; }
        size_t m; const uint64_t *v = rec_words(f->acc3, &m);
        W.L.word_compares++;
        if (f->i < m) { if (v[f->i] != f->buf.w[f->i]) { f->j = (f->j + 1) & (t->nslots - 1); f->ph = 1; return; } f->i++; return; }
        fin(o, f->acc3); return;
    }
    }
}
static Frame fr_intern(const uint64_t *w, size_t n) { Frame f = fr(OF_INTERN, 0, 0, 0, 0); words_append(&f.buf, w, n); return f; }
/* §94.2(1): a frame's exclusive buffer becomes the child's key in constant
 * work (ownership transfer, no copy); the donor is left empty */
static void words_take(Words *dst, Words *src) { words_free(dst); *dst = *src; words_init(src); }
static Frame fr_intern_own(Words *w) { Frame f = fr(OF_INTERN, 0, 0, 0, 0); words_take(&f.buf, w); return f; }
static Frame fr_lookup(const uint64_t *w, size_t n) { Frame f = fr(OF_LOOKUP, 0, 0, 0, 0); words_append(&f.buf, w, n); return f; }
static void push_intern(Op *o, const uint64_t *w, size_t n) { push(o, fr_intern(w, n)); }
static void push_intern_own(Op *o, Words *w) { push(o, fr_intern_own(w)); }
static void push_lookup(Op *o, const uint64_t *w, size_t n) { W.L.memo_lookup++; push(o, fr_lookup(w, n)); }

/* ---------------------------------------------------------------- 3. atoms, sets, formulas ---- */

static AtomId atom_intern(const uint64_t *w, size_t n) { LOCK; uint64_t id = intern_sync(w, n, NULL); UNLOCK; return id; }
/* §81.1: a producer identity names the actual shared producer instance:
 * the structural computation (shape), the projected face, and the snapshot
 * the instance belongs to (its creation environment when an instance for
 * this key exists and is reusable now; otherwise the current one) */
static AtomId atom_producer_at(ShapeId s, FaceId eta, uint64_t env) {
    uint64_t w[5] = { K_ATOM, WK_PRODUCER, s, eta, env };
    return atom_intern(w, 5);
}
static AtomId atom_producer_ref(RefId t, FaceId chi) {
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    FaceId eta = fc_project(chi, S, n); W.L.kernel_calls += 2;
    LOCK; KernelMark km = kernel_mark(); UNLOCK;
    EntryId e = eval_entry_lookup(t, eta); ShapeId sh = shape_of(t);
    LOCK; kernel_charge(km); UNLOCK;
    AtomId a = atom_producer_at(sh, eta, e ? eval_entry_env(e) : global_env_version());
    LOCK; if (!side(a)->val) side(a)->val = t; UNLOCK;    /* a representative reference for specialization (not part of the identity) */
    return a;
}
AtomId atom_producer(RefId t, FaceId chi) { return atom_producer_ref(t, chi); }
AtomId atom_request(AtomId owner, uint64_t slot, AtomId child) { uint64_t w[5] = { K_ATOM, WK_REQUEST, owner, slot, child }; return atom_intern(w, 5); }
AtomId atom_deliver(AtomId owner, uint64_t slot, AtomId child) { uint64_t w[5] = { K_ATOM, WK_DELIVER, owner, slot, child }; return atom_intern(w, 5); }
AtomId atom_pub(AtomId producer) { uint64_t w[3] = { K_ATOM, WK_PUB, producer }; return atom_intern(w, 3); }
AtomId atom_eval(AtomId producer, uint64_t ordinal) { uint64_t w[4] = { K_ATOM, WK_EVAL, producer, ordinal }; return atom_intern(w, 4); }
AtomId atom_apply(uint64_t transform, int dir, MapId sigma, RefId arg, AtomId receiver, uint64_t ordinal) { uint64_t w[8] = { K_ATOM, WK_APPLY, transform, (uint64_t)dir, sigma, arg, receiver, ordinal }; return atom_intern(w, 8); }
AtomId atom_slot(uint64_t index) { uint64_t w[3] = { K_ATOM, WK_SLOT, index }; return atom_intern(w, 3); }
AtomId atom_named(uint64_t name) { uint64_t w[3] = { K_ATOM, WK_NAMED, name }; return atom_intern(w, 3); }
AtomKind atom_kind(AtomId a) { require(rec_kind(a) == K_ATOM, "not an atom"); return (AtomKind)rec_w(a, 1); }
const uint64_t *atom_words(AtomId a, size_t *n) { const uint64_t *w = rec_words(a, n); (*n)--; return w + 1; }

static int cmp_counted(const void *a, const void *b) { W.L.word_compares++; uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y ? 1 : 0; }
static void sort_counted(uint64_t *p, size_t n) { if (n > 1) qsort(p, n, sizeof(uint64_t), cmp_counted); }
static SetId set_intern_sorted(const uint64_t *atoms, size_t n) { Words w; words_init(&w); words_push(&w, K_SET); words_append(&w, atoms, n); uint64_t id = intern_sync(w.w, w.n, NULL); words_free(&w); return id; }
SetId set_make(size_t n, const AtomId *atoms) {
    LOCK;
    uint64_t *c = n ? malloc(n * sizeof(uint64_t)) : NULL; require(!n || c, "out of memory");
    if (n) memcpy(c, atoms, n * sizeof(uint64_t));
    sort_counted(c, n);
    size_t m = 0; for (size_t i = 0; i < n; i++) { charge(FR_SUPPORT_CHUNK); if (!m || c[m - 1] != c[i]) c[m++] = c[i]; }
    SetId s = set_intern_sorted(c, m); free(c);
    UNLOCK; return s;
}
size_t set_size(SetId s) { size_t n; rec_words(s, &n); return n - 1; }
const AtomId *set_atoms(SetId s, size_t *n) { const uint64_t *w = rec_words(s, n); require(w[0] == K_SET, "not a set"); (*n)--; return w + 1; }
bool set_has(SetId s, AtomId a) { size_t n; const AtomId *x = set_atoms(s, &n); size_t lo = 0, hi = n; while (lo < hi) { size_t mid = (lo + hi) / 2; W.L.word_compares++; charge(FR_SUPPORT_CHUNK); if (x[mid] == a) return true; if (x[mid] < a) lo = mid + 1; else hi = mid; } return false; }
SetId set_empty(void) { return W.EMPTY; }

/* formulas: [K_FORMULA, tag, l, r] with ATOM(e) = [K_FORMULA, FM_ATOM, e, 0] */
FormulaId formula_zero(void) { return W.ZERO; }
FormulaId formula_one(void) { return W.ONE; }
FormulaTag formula_tag(FormulaId f) { require(rec_kind(f) == K_FORMULA, "not a formula"); return (FormulaTag)rec_w(f, 1); }
AtomId formula_atom_of(FormulaId f) { require(formula_tag(f) == FM_ATOM, "not an atom formula"); return rec_w(f, 2); }
FormulaId formula_left(FormulaId f) { return rec_w(f, 2); }
FormulaId formula_right(FormulaId f) { return rec_w(f, 3); }

/* MKF: a = tag, b = l, c = r. Constructor simplifications (§68.1) then INTERN. */
static void step_mkf(Op *o, Frame *f) {
    if (f->ph == 0) {
        uint64_t tag = f->a, l = f->b, r = f->c;
        if (tag == FM_AND) {
            if (l == W.ZERO || r == W.ZERO) { fin(o, W.ZERO); return; }
            if (l == W.ONE) { fin(o, r); return; }
            if (r == W.ONE) { fin(o, l); return; }
            if (l == r) { fin(o, l); return; }
        } else if (tag == FM_OR) {
            if (l == W.ONE || r == W.ONE) { fin(o, W.ONE); return; }
            if (l == W.ZERO) { fin(o, r); return; }
            if (r == W.ZERO) { fin(o, l); return; }
            if (l == r) { fin(o, l); return; }
        }
        uint64_t w[4] = { K_FORMULA, tag, l, r };
        f->ph = 1; push_intern(o, w, 4); return;
    }
    fin(o, o->ret);
}
static Frame fr_mkf(uint64_t tag, FormulaId l, FormulaId r) { return fr(OF_MKF, tag, l, r, 0); }
FormulaId formula_atom(AtomId a) { LOCK; FormulaId f = run_op(OF_MKF, PH_REWRITE, fr_mkf(FM_ATOM, a, 0), NULL); UNLOCK; return f; }
FormulaId formula_and(FormulaId l, FormulaId r) { LOCK; FormulaId f = run_op(OF_MKF, PH_REWRITE, fr_mkf(FM_AND, l, r), NULL); UNLOCK; return f; }
FormulaId formula_or(FormulaId l, FormulaId r) { LOCK; FormulaId f = run_op(OF_MKF, PH_REWRITE, fr_mkf(FM_OR, l, r), NULL); UNLOCK; return f; }
OpId op_formula_and(FormulaId l, FormulaId r) { LOCK; OpId h = op_new(OF_MKF, PH_REWRITE, fr_mkf(FM_AND, l, r)); UNLOCK; return h; }
OpId op_formula_or(FormulaId l, FormulaId r) { LOCK; OpId h = op_new(OF_MKF, PH_REWRITE, fr_mkf(FM_OR, l, r)); UNLOCK; return h; }

/* RESTRICT: a = F, b = e, c = bit. ENTER(0) → memo LOOKUP(1) → left(2) → right(3) → REBUILD(4) → memo PUT(5) → done */
static void step_restrict(Op *o, Frame *f) {
    FormulaId F = f->a;
    switch (f->ph) {
    case 0: {
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO || t == FM_ONE) { fin(o, F); return; }
        if (t == FM_ATOM) { fin(o, formula_atom_of(F) == f->b ? (f->c ? W.ONE : W.ZERO) : F); return; }
        uint64_t k[4] = { K_MEMO, F, f->b, f->c };
        f->ph = 1; push_lookup(o, k, 4); return;
    }
    case 1:
        if (o->ret && side(o->ret)->has_val) { W.L.memo_hit++; W.L.memo_deliver++; fin(o, side(o->ret)->val); return; }
        f->ph = 2; push(o, fr(OF_RESTRICT, formula_left(F), f->b, f->c, 0)); return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_RESTRICT, formula_right(F), f->b, f->c, 0)); return;
    case 3: f->acc2 = o->ret; f->ph = 4; push(o, fr_mkf(formula_tag(F), f->acc, f->acc2)); return;
    case 4: { f->acc3 = o->ret; uint64_t k[4] = { K_MEMO, F, f->b, f->c }; f->ph = 5; push_intern(o, k, 4); return; }
    case 5: { Side *s = side(o->ret); s->val = f->acc3; s->has_val = true; fin(o, f->acc3); return; }
    }
}
FormulaId formula_restrict(FormulaId F, AtomId e, int bit) { LOCK; FormulaId r = run_op(OF_RESTRICT, PH_REWRITE, fr(OF_RESTRICT, F, e, bit ? 1 : 0, 0), NULL); UNLOCK; return r; }
OpId op_restrict(FormulaId F, AtomId e, int bit) { LOCK; OpId h = op_new(OF_RESTRICT, PH_REWRITE, fr(OF_RESTRICT, F, e, bit ? 1 : 0, 0)); UNLOCK; return h; }

/* SUPPORT / MUST: a = F; cached per formula record. ENTER(0) → left(1) → right(2) → MERGE(3, one element per step) → INTERN(4) → done.
 * MUST: AND = union, OR = intersection; ZERO is rejected (nonzero formulas only). */
static void step_support(Op *o, Frame *f) {
    FormulaId F = f->a; bool must = f->fam == OF_MUST;
    Side *s = side(F);
    switch (f->ph) {
    case 0: {
        SetId cached = must ? s->must : s->support;
        W.L.memo_lookup++;
        if (cached) { W.L.memo_hit++; W.L.memo_deliver++; fin(o, cached); return; }
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO) { if (must) { fail(o, "Must is defined on nonzero formulas only"); return; } fin(o, W.EMPTY); return; }
        if (t == FM_ONE) { fin(o, W.EMPTY); return; }
        if (t == FM_ATOM) { uint64_t w[2] = { K_SET, formula_atom_of(F) }; f->ph = 4; push_intern(o, w, 2); return; }
        f->ph = 1; push(o, fr(f->fam, formula_left(F), 0, 0, 0)); return;
    }
    case 1: f->acc = o->ret; f->ph = 2; push(o, fr(f->fam, formula_right(F), 0, 0, 0)); return;
    case 2: f->acc2 = o->ret; f->i = f->j = 0; f->ph = 3; words_push(&f->buf, K_SET); return;
    case 3: {
        size_t na, nb; const AtomId *A = set_atoms(f->acc, &na), *B = set_atoms(f->acc2, &nb);
        bool inter = must && formula_tag(F) == FM_OR;
        W.L.word_compares++;
        if (f->i < na && f->j < nb) {
            if (A[f->i] == B[f->j]) { words_push(&f->buf, A[f->i]); f->i++; f->j++; }
            else if (A[f->i] < B[f->j]) { if (!inter) words_push(&f->buf, A[f->i]); f->i++; }
            else { if (!inter) words_push(&f->buf, B[f->j]); f->j++; }
            return;
        }
        if (!inter) { if (f->i < na) { words_push(&f->buf, A[f->i++]); return; } if (f->j < nb) { words_push(&f->buf, B[f->j++]); return; } }
        f->ph = 4; push_intern_own(o, &f->buf); return;
    }
    case 4: if (must) s->must = o->ret; else s->support = o->ret; fin(o, o->ret); return;
    }
}
SetId formula_support(FormulaId F) { LOCK; SetId s = run_op(OF_SUPPORT, PH_REWRITE, fr(OF_SUPPORT, F, 0, 0, 0), NULL); UNLOCK; return s; }
SetId formula_must(FormulaId F) { LOCK; SetId s = run_op(OF_MUST, PH_REWRITE, fr(OF_MUST, F, 0, 0, 0), NULL); UNLOCK; return s; }
OpId op_support(FormulaId F) { LOCK; OpId h = op_new(OF_SUPPORT, PH_REWRITE, fr(OF_SUPPORT, F, 0, 0, 0)); UNLOCK; return h; }
OpId op_must(FormulaId F) { LOCK; OpId h = op_new(OF_MUST, PH_REWRITE, fr(OF_MUST, F, 0, 0, 0)); UNLOCK; return h; }

/* SUBST: a = F, b = set M, c = bit: one RESTRICT per atom */
static void step_subst(Op *o, Frame *f) {
    size_t n; const AtomId *M = set_atoms(f->b, &n);
    if (f->ph == 0) { f->acc = f->a; f->ph = 1; }
    else f->acc = o->ret;
    if (f->i < n) { AtomId e = M[f->i++]; push(o, fr(OF_RESTRICT, f->acc, e, f->c, 0)); return; }
    fin(o, f->acc);
}
FormulaId formula_subst(FormulaId F, SetId M, int bit) { LOCK; FormulaId r = run_op(OF_SUBST, PH_REWRITE, fr(OF_SUBST, F, M, bit ? 1 : 0, 0), NULL); UNLOCK; return r; }

/* SETOP: a = kind, b = A, c = B: merge one element per step then INTERN */
static void step_setop(Op *o, Frame *f) {
    size_t na, nb; const AtomId *A = set_atoms(f->b, &na), *B = set_atoms(f->c, &nb);
    if (f->ph == 0) { words_push(&f->buf, K_SET); f->ph = 1; return; }
    if (f->ph == 2) { fin(o, o->ret); return; }
    W.L.word_compares++;
    if (f->i < na && f->j < nb) {
        AtomId x = A[f->i], y = B[f->j];
        if (x == y) { if (f->a != SO_DIFF) words_push(&f->buf, x); f->i++; f->j++; }
        else if (x < y) { if (f->a != SO_INTER) words_push(&f->buf, x); f->i++; }
        else { if (f->a == SO_UNION) words_push(&f->buf, y); f->j++; }
        return;
    }
    if (f->i < na) { if (f->a != SO_INTER) words_push(&f->buf, A[f->i]); f->i++; return; }
    if (f->j < nb) { if (f->a == SO_UNION) words_push(&f->buf, B[f->j]); f->j++; return; }
    f->ph = 2; push_intern_own(o, &f->buf);
}
static SetId setop(int kind, SetId a, SetId b) { return run_op(OF_SETOP, W.phase, fr(OF_SETOP, kind, a, b, 0), NULL); }
SetId set_union(SetId a, SetId b) { LOCK; SetId s = setop(SO_UNION, a, b); UNLOCK; return s; }
SetId set_inter(SetId a, SetId b) { LOCK; SetId s = setop(SO_INTER, a, b); UNLOCK; return s; }
SetId set_diff(SetId a, SetId b) { LOCK; SetId s = setop(SO_DIFF, a, b); UNLOCK; return s; }
/* SUBSET: a = A, b = B: merge-walk; result 1/0 */
static void step_subset(Op *o, Frame *f) {
    size_t na, nb; const AtomId *A = set_atoms(f->a, &na), *B = set_atoms(f->b, &nb);
    W.L.word_compares++;
    if (f->i >= na) { fin(o, 1); return; }
    if (f->j >= nb) { fin(o, 0); return; }
    if (A[f->i] == B[f->j]) { f->i++; f->j++; return; }
    if (A[f->i] < B[f->j]) { fin(o, 0); return; }
    f->j++;
}
static bool subset_locked(SetId a, SetId b) { return run_op(OF_SUBSET, W.phase, fr(OF_SUBSET, a, b, 0, 0), NULL) == 1; }
bool set_subset(SetId a, SetId b) { LOCK; bool r = subset_locked(a, b); UNLOCK; return r; }
bool set_disjoint(SetId a, SetId b) { LOCK; SetId i = setop(SO_INTER, a, b); UNLOCK; return i == W.EMPTY; }

/* SUM: a = set, b = model: per atom, weight lookup (override table then kind weight), checked add */
static Cost kind_weight(ModelId m, AtomId a);
static void step_sum(Op *o, Frame *f) {
    size_t n; const AtomId *S = set_atoms(f->a, &n);
    switch (f->ph) {
    case 0:
        if (f->i >= n) { fin(o, f->acc); return; }
        { uint64_t k[3] = { K_WEIGHT, f->b, S[f->i] }; f->ph = 1; push_lookup(o, k, 3); return; }
    case 1: {
        Cost w = (o->ret && side(o->ret)->has_val) ? side(o->ret)->val : kind_weight(f->b, S[f->i]);
        if (o->ret && side(o->ret)->has_val) { W.L.memo_hit++; W.L.memo_deliver++; }
        Cost r; if (!add_checked(f->acc, w, &r)) { limit(o, "cost sum not representable in the checked natural range"); return; }
        f->acc = r; f->i++; f->ph = 0; return;
    }
    }
}
Cost set_weight(SetId s, ModelId m, bool *overflow) {
    LOCK; Op *o = job_sync(fr(OF_SUM, s, m, 0, 0));
    uint64_t r = run_locked(o, NULL); bool ov = o->st == OP_RESOURCE_LIMIT;
    UNLOCK; if (overflow) *overflow = ov; return ov ? COST_MAX : r;
}
OpId op_set_weight(SetId s, ModelId m) { LOCK; OpId h = op_new(OF_SUM, PH_REWRITE, fr(OF_SUM, s, m, 0, 0)); UNLOCK; return h; }

/* SORT: a = record kind (K_SET / K_FAMILY), buf = elements. In-place heap
 * sort — one sift per frame (at most 64 compares and swaps, the heap depth of
 * a 64-bit index space) — then one element per frame of deduplication, then
 * the record is interned. The bounded API never sorts inside one frame. */
static void sift_down(uint64_t *h, size_t n, size_t i) {
    for (;;) { size_t l = 2 * i + 1, r = l + 1, m = i; W.L.word_compares += 2; if (l < n && h[l] > h[m]) m = l; if (r < n && h[r] > h[m]) m = r; if (m == i) return; uint64_t t = h[i]; h[i] = h[m]; h[m] = t; i = m; }
}
static void step_sort(Op *o, Frame *f) {
    size_t n = f->buf.n;
    switch (f->ph) {
    case 0: if (n < 2) { f->ph = 2; f->i = 0; f->j = 0; return; } f->i = n / 2; f->ph = 1; return;
    case 1:   /* build: sift index i-1; then extract from the end */
        if (f->i > 0) { f->i--; sift_down(f->buf.w, n, f->i); return; }
        if (f->j == 0) f->j = n;
        if (f->j > 1) { f->j--; uint64_t t = f->buf.w[0]; f->buf.w[0] = f->buf.w[f->j]; f->buf.w[f->j] = t; sift_down(f->buf.w, f->j, 0); return; }
        f->ph = 2; f->i = 0; f->j = 0; return;
    case 2:   /* dedupe: buf2 collects */
        if (f->j == 0) { words_push(&f->buf2, f->a); f->j = 1; }
        if (f->i < n) { W.L.word_compares++; if (f->buf2.n == 1 || f->buf2.w[f->buf2.n - 1] != f->buf.w[f->i]) words_push(&f->buf2, f->buf.w[f->i]); f->i++; return; }
        f->ph = 3; push_intern_own(o, &f->buf2); return;
    case 3: fin(o, o->ret); return;
    }
}
static Frame fr_sort_own(uint64_t kind, Words *w) { Frame f = fr(OF_SORT, kind, 0, 0, 0); words_take(&f.buf, w); return f; }

/* LIST: a list record [K_LIST, words...] from buf (used for ordered atom lists) */
static void step_list(Op *o, Frame *f) { if (f->ph == 0) { f->ph = 1; push_intern_own(o, &f->buf); return; } fin(o, o->ret); }

/* ---------------------------------------------------------------- 4. demand (§60) ---- */

typedef struct { AtomId producer; uint64_t steps; bool alias; VEC(AtomId) occ; VEC(uint64_t) applies; } DNode;   /* applies: indices into graph applies */
typedef struct { uint64_t transform; int dir; MapId sigma; RefId arg; AtomId receiver; } DApply;
struct DGraph { VEC(DNode) nodes; VEC(AtomId) roots; VEC(DApply) applies; uint64_t rev; WordMap index; /* producer → node index + 1 (fixed-size key: a bounded probe) */ };
static uint64_t dgraph_rev(const DGraph *g) { return g->rev; }
typedef struct { VEC(AtomId) producers; VEC(Occurrence) occ; } Demand;
typedef struct { SetId atoms; WorkCounts counts; } WorkSetInfo;

static DGraph *DG(DGraphId g) { require(rec_kind(g) == K_DGRAPH, "not a demand graph"); return (DGraph *)side(g)->ptr; }
DGraphId dgraph_new(void) {
    LOCK; static uint64_t seq; uint64_t w[2] = { K_DGRAPH, ++seq }; DGraphId g = intern_sync(w, 2, NULL);
    DGraph *d = own(calloc(1, sizeof *d)); require(d, "out of memory"); wordmap_init(&d->index); side(g)->ptr = d; charge(FR_ALLOCATE_CHUNK); UNLOCK; return g;
}
static DNode *dnode(DGraph *d, AtomId p) { uint64_t k[1] = { p }, v; W.L.probes++; if (!wordmap_get(&d->index, k, 1, &v)) return NULL; return &d->nodes.data[v - 1]; }
void dgraph_add_producer(DGraphId g, AtomId producer, uint64_t steps) {
    LOCK; DGraph *d = DG(g); require(!dnode(d, producer), "producer already in the graph");
    DNode n; memset(&n, 0, sizeof n); n.producer = producer; n.steps = steps; vec_push(&d->nodes, n); { uint64_t k[1] = { producer }; wordmap_put(&d->index, k, 1, d->nodes.len); } d->rev++; charge(FR_ALLOCATE_CHUNK); UNLOCK;
}
void dgraph_add_occurrence(DGraphId g, AtomId owner, AtomId child) { LOCK; DGraph *d = DG(g); DNode *n = dnode(d, owner); require(n, "occurrence of an unknown owner"); vec_push(&n->occ, child); d->rev++; charge(FR_ALLOCATE_CHUNK); UNLOCK; }
void dgraph_add_apply(DGraphId g, AtomId receiver, uint64_t transform, int dir, MapId sigma, RefId arg) {
    LOCK; DGraph *d = DG(g); DNode *n = dnode(d, receiver); require(n, "identity application received by an unknown producer");
    DApply a = { transform, dir, sigma, arg, receiver }; vec_push(&d->applies, a); vec_push(&n->applies, d->applies.len - 1); d->rev++; charge(FR_ALLOCATE_CHUNK); UNLOCK;
}
void dgraph_mark_alias(DGraphId g, AtomId producer) { LOCK; DGraph *d = DG(g); DNode *n = dnode(d, producer); require(n, "unknown producer"); n->alias = true; d->rev++; UNLOCK; }
void dgraph_add_root(DGraphId g, AtomId root) { LOCK; DGraph *d = DG(g); vec_push(&d->roots, root); d->rev++; charge(FR_ALLOCATE_CHUNK); UNLOCK; }
size_t dgraph_roots(DGraphId g, const AtomId **out) { DGraph *d = DG(g); *out = d->roots.data; return d->roots.len; }
SetId work_ready_snapshot(void) {
    size_t n = eval_entry_count(); Words w; words_init(&w);
    for (size_t i = 1; i <= n; i++) if (eval_entry_state(i) == E_READY) words_push(&w, atom_producer_at(eval_entry_shape(i), eval_entry_face(i), eval_entry_env(i)));
    SetId s = set_make(w.n, w.w); words_free(&w); return s;
}

DGraphId dgraph_from_trace(void) { return dgraph_from_trace_since(0); }
DGraphId dgraph_from_trace_since(size_t first_root) {
    DGraphId g = dgraph_new();
    size_t n = eval_entry_count();
    AtomId *key = n ? malloc(n * sizeof(AtomId)) : NULL; require(!n || key, "out of memory");
    for (size_t i = 1; i <= n; i++) { key[i - 1] = atom_producer_at(eval_entry_shape(i), eval_entry_face(i), eval_entry_env(i)); { LOCK; if (!side(key[i - 1])->val) side(key[i - 1])->val = eval_entry_ref(i); UNLOCK; } dgraph_add_producer(g, key[i - 1], eval_entry_steps(i)); if (eval_entry_is_alias(i)) dgraph_mark_alias(g, key[i - 1]); }
    for (size_t i = 1; i <= n; i++) {
        EntryId *deps; size_t m = eval_entry_deps(i, &deps);
        for (size_t k = 0; k < m; k++) dgraph_add_occurrence(g, key[i - 1], key[deps[k] - 1]);
        free(deps);
    }
    EntryId *roots; size_t nr = eval_root_occurrences(&roots);
    for (size_t k = first_root; k < nr; k++) dgraph_add_root(g, key[roots[k] - 1]);
    free(roots);
    Net *net = eval_net(); size_t nt = net_trace_count(net);
    for (size_t k = 0; k < nt; k++) { NetTraceEvent e = net_trace_get(net, k); if (e.kind == NT_APPLY_TRANSFORM && e.K) dgraph_add_apply(g, key[e.K - 1], e.transform, e.dir, e.sigma, e.arg); }
    free(key);
    return g;
}

/* DEMAND: a = graph, b = roots, c = ready. Marks are per-operation records
 * [K_MARK, op mark, tag, key]. ph0: mark ready atoms (i); ph1: roots (i):
 * each root is an occurrence; uncached and unvisited roots enter the
 * worklist; ph2: pop a producer, record it, walk its occurrences (j);
 * each child occurrence is recorded; an unready, unvisited child enters once. */
static void step_demand(Op *o, Frame *f) {
    DGraph *d = DG(f->a); Demand *dm = (Demand *)f->acc4;
    size_t nr, nk; const AtomId *R = set_atoms(f->b, &nr), *K = set_atoms(f->c, &nk);
    switch (f->ph) {
    case 0: {
        if (!dm) { dm = own(calloc(1, sizeof *dm)); require(dm, "out of memory"); f->acc4 = (uint64_t)(uintptr_t)dm; }
        if (f->i < nk) { uint64_t k[4] = { K_MARK, o->id, 1, K[f->i++] }; push_intern(o, k, 4); return; }
        f->i = 0; f->ph = 1; return;
    }
    case 1: {   /* root occurrences: the graph's root list (ordered) filtered to the requested roots set */
        if (f->i < d->roots.len) {
            AtomId r = d->roots.data[f->i];
            if (!set_has(f->b, r)) { f->i++; return; }
            Occurrence oc = { 0, f->i, r }; vec_push(&dm->occ, oc); charge(FR_ALLOCATE_CHUNK);
            uint64_t k[4] = { K_MARK, o->id, 1, r }; f->ph = 10; push_lookup(o, k, 4); return;
        }
        (void)R; f->ph = 2; return;
    }
    case 10: {  /* ready? → cut (the occurrence stays, the producer cone is not entered) */
        AtomId r = d->roots.data[f->i];
        if (o->ret) { W.L.memo_hit++; f->i++; f->ph = 1; return; }
        uint64_t k[4] = { K_MARK, o->id, 2, r }; f->ph = 11; push_intern(o, k, 4); return;
    }
    case 11: {
        AtomId r = d->roots.data[f->i];
        Side *s = side(o->ret);
        if (!s->has_val) { s->has_val = true; words_push(&f->buf, r); }
        f->i++; f->ph = 1; return;
    }
    case 2: {   /* pop */
        if (f->buf.n <= f->acc) { uint64_t w[5] = { K_DEMAND, f->a, f->b, f->c, dgraph_rev(d) }; f->ph = 6; push_intern(o, w, 5); return; }
        f->acc2 = f->buf.w[f->acc++];
        vec_push(&dm->producers, f->acc2); charge(FR_ALLOCATE_CHUNK);
        f->j = 0; f->ph = 3; return;
    }
    case 3: {   /* next occurrence of the popped producer */
        DNode *n = dnode(d, f->acc2);
        if (!n) { fail(o, "demanded producer has no recipe in the graph"); return; }
        if (f->j >= n->occ.len) { f->ph = 2; return; }
        AtomId child = n->occ.data[f->j];
        Occurrence oc = { f->acc2, f->j, child }; vec_push(&dm->occ, oc); charge(FR_ALLOCATE_CHUNK);
        uint64_t k[4] = { K_MARK, o->id, 1, child }; f->ph = 4; push_lookup(o, k, 4); return;
    }
    case 4: {
        DNode *n = dnode(d, f->acc2); AtomId child = n->occ.data[f->j];
        if (o->ret) { W.L.memo_hit++; f->j++; f->ph = 3; return; }           /* ready child: cut */
        uint64_t k[4] = { K_MARK, o->id, 2, child }; f->ph = 5; push_intern(o, k, 4); return;
    }
    case 5: {
        DNode *n = dnode(d, f->acc2); AtomId child = n->occ.data[f->j];
        Side *s = side(o->ret);
        if (!s->has_val) { s->has_val = true; words_push(&f->buf, child); }
        f->j++; f->ph = 3; return;
    }
    case 6: if (!side(o->ret)->ptr) side(o->ret)->ptr = dm; fin(o, o->ret); return;
    }
}
DemandId demand_closure(DGraphId g, SetId roots, SetId ready) {
    LOCK; const char *why; DemandId id = run_op(OF_DEMAND, PH_PREPARE, fr(OF_DEMAND, g, roots, ready, 0), &why);
    require(id, "demand closure: %s", why);
    UNLOCK; return id;
}
OpId op_demand(DGraphId g, SetId roots, SetId ready) { LOCK; OpId h = op_new(OF_DEMAND, PH_PREPARE, fr(OF_DEMAND, g, roots, ready, 0)); UNLOCK; return h; }
static Demand *DM(DemandId d) { require(rec_kind(d) == K_DEMAND, "not a demand"); return (Demand *)side(d)->ptr; }
size_t demand_producers(DemandId d, const AtomId **out) { Demand *m = DM(d); *out = m->producers.data; return m->producers.len; }
size_t demand_occurrences(DemandId d, const Occurrence **out) { Demand *m = DM(d); *out = m->occ.data; return m->occ.len; }

/* EXTRACT: a = demand. ph0: occurrences (i): REQUEST then DELIVER atoms; ph1: producers (i): PUB, EVAL steps (j), applies (j2); ph2: sort + intern set */
static void step_extract(Op *o, Frame *f) {
    Demand *dm = DM(f->a); DGraph *d = DG(rec_w(f->a, 1));
    WorkSetInfo *wi = (WorkSetInfo *)(uintptr_t)f->acc4;
    if (!wi) { wi = own(calloc(1, sizeof *wi)); require(wi, "out of memory"); f->acc4 = (uint64_t)(uintptr_t)wi; }
    switch (f->ph) {
    case 0:
        if (f->i < dm->occ.len) {
            Occurrence oc = dm->occ.data[f->i];
            uint64_t w[5] = { K_ATOM, f->j == 0 ? WK_REQUEST : WK_DELIVER, oc.owner, oc.slot, oc.child };
            f->ph = 20; push_intern(o, w, 5); return;
        }
        f->i = 0; f->j = 0; f->ph = 1; return;
    case 20:
        words_push(&f->buf, o->ret);
        if (f->j == 0) { wi->counts.request++; f->j = 1; } else { wi->counts.deliver++; f->j = 0; f->i++; }
        f->ph = 0; return;
    case 1: {
        if (f->i >= dm->producers.len) { f->ph = 2; return; }
        AtomId p = dm->producers.data[f->i]; DNode *n = dnode(d, p);
        if (f->j == 0) { if (n->alias) { f->j = 1; return; } uint64_t w[3] = { K_ATOM, WK_PUB, p }; f->ph = 21; push_intern(o, w, 3); return; }   /* an alias publication ran no producer */
        if (f->j - 1 < n->steps) { uint64_t w[4] = { K_ATOM, WK_EVAL, p, f->j - 1 }; f->ph = 22; push_intern(o, w, 4); return; }
        size_t ka = f->j - 1 - n->steps;
        if (ka < n->applies.len) {
            DApply a = d->applies.data[n->applies.data[ka]];
            uint64_t w[8] = { K_ATOM, WK_APPLY, a.transform, (uint64_t)a.dir, a.sigma, a.arg, a.receiver, n->applies.data[ka] };
            f->ph = 23; push_intern(o, w, 8); return;
        }
        f->i++; f->j = 0; return;
    }
    case 21: words_push(&f->buf, o->ret); wi->counts.pub++; f->j++; f->ph = 1; return;
    case 22: words_push(&f->buf, o->ret); wi->counts.eval++; f->j++; f->ph = 1; return;
    case 23: words_push(&f->buf, o->ret); wi->counts.apply++; f->j++; f->ph = 1; return;
    case 2: f->ph = 3; push(o, fr_sort_own(K_SET, &f->buf)); return;
    case 3: {
        wi->atoms = o->ret;
        uint64_t w[3] = { K_WORKSET, f->a, o->ret };
        f->ph = 4; push_intern(o, w, 3); return;
    }
    case 4: if (!side(o->ret)->ptr) side(o->ret)->ptr = wi; fin(o, o->ret); return;
    }
}
WorkSetId work_extract(DemandId d) { LOCK; const char *why; WorkSetId w = run_op(OF_EXTRACT, PH_PREPARE, fr(OF_EXTRACT, d, 0, 0, 0), &why); require(w, "extract: %s", why); UNLOCK; return w; }
OpId op_extract(DemandId d) { LOCK; OpId h = op_new(OF_EXTRACT, PH_PREPARE, fr(OF_EXTRACT, d, 0, 0, 0)); UNLOCK; return h; }
static WorkSetInfo *WI(WorkSetId w) { require(rec_kind(w) == K_WORKSET, "not a work set"); return (WorkSetInfo *)side(w)->ptr; }
SetId workset_atoms(WorkSetId w) { return WI(w)->atoms; }
WorkCounts workset_counts(WorkSetId w) { return WI(w)->counts; }

/* ---------------------------------------------------------------- 5. specialization (§62), algebra (§61), differences (§63) ---- */

/* ATOMSPEC: a = atom, b = σ. Reindex the complete typed boundary of the
 * work identity, validate it, project the face, intern the image (§62.1).
 * Composite identities specialize their component identities first. */
static void step_atomspec(Op *o, Frame *f) {
    size_t n; const uint64_t *w = rec_words(f->a, &n);
    AtomKind k = (AtomKind)w[1];
    switch (f->ph) {
    case 0:
        switch (k) {
        case WK_PRODUCER: {
            RefId src_ref = (RefId)side(f->a)->val; if (!src_ref) { fail(o, "producer identity without a representative reference"); return; }
            RefId t = reindex(src_ref, f->b); W.L.kernel_calls++;
            const char *why = NULL;
            if (!ref_validate(t, &why)) { fail(o, "specialized reference fails structural validation"); return; }
            W.L.kernel_calls++;
            FaceId chi = fc_reindex(w[3], f->b); size_t ns; const uint64_t *S = dimset_get(ref_support(t), &ns);
            FaceId eta = fc_project(chi, S, ns); W.L.kernel_calls += 2;
            if (!fc_entails(eta, ref_required(t))) { fail(o, "specialized occurrence outside its required face"); return; }
            { KernelMark km = kernel_mark(); EntryId ex = eval_entry_lookup(t, eta); ShapeId sh = shape_of(t); kernel_charge(km);
              uint64_t v[5] = { K_ATOM, WK_PRODUCER, sh, eta, ex ? eval_entry_env(ex) : global_env_version() };
              f->acc4 = t; f->ph = 9; push_intern(o, v, 5); return; }
        }
        case WK_REQUEST: case WK_DELIVER:
            if (w[2]) { f->ph = 1; push(o, fr(OF_ATOMSPEC, w[2], f->b, 0, 0)); return; }
            f->acc = 0; f->ph = 2; push(o, fr(OF_ATOMSPEC, w[4], f->b, 0, 0)); return;
        case WK_PUB: case WK_EVAL: f->ph = 3; push(o, fr(OF_ATOMSPEC, w[2], f->b, 0, 0)); return;
        case WK_APPLY: f->ph = 4; push(o, fr(OF_ATOMSPEC, w[6], f->b, 0, 0)); return;
        default: fin(o, f->a); return;
        }
    case 1: f->acc = o->ret; f->ph = 2; push(o, fr(OF_ATOMSPEC, w[4], f->b, 0, 0)); return;
    case 2: { uint64_t v[5] = { K_ATOM, k, f->acc, w[3], o->ret }; f->ph = 9; push_intern(o, v, 5); return; }
    case 3: { uint64_t v[4] = { K_ATOM, k, o->ret, w[3] }; f->ph = 9; push_intern(o, v, k == WK_PUB ? 3 : 4); return; }
    case 4: { W.L.kernel_calls += 2; uint64_t v[8] = { K_ATOM, WK_APPLY, w[2], w[3], compose(w[4], f->b), reindex(w[5], f->b), o->ret, w[7] }; f->ph = 9; push_intern(o, v, 8); return; }
    case 9: if (k == WK_PRODUCER && f->acc4 && !side(o->ret)->val) side(o->ret)->val = f->acc4; fin(o, o->ret); return;
    }
}
/* SPEC_SET: a = set, b = σ: image of every element, then sort/dedupe (the Boolean direct image s_!) */
static void step_spec_set(Op *o, Frame *f) {
    size_t n; const AtomId *S = set_atoms(f->a, &n);
    switch (f->ph) {
    case 0: if (f->i < n) { f->ph = 1; push(o, fr(OF_ATOMSPEC, S[f->i], f->b, 0, 0)); return; } f->ph = 2; return;
    case 1: words_push(&f->buf, o->ret); f->i++; f->ph = 0; return;
    case 2: f->ph = 3; push(o, fr_sort_own(K_SET, &f->buf)); return;
    case 3: fin(o, o->ret); return;
    }
}
SetId set_specialize(SetId s, MapId sigma, const char **why) { LOCK; SetId r = run_op(OF_SPEC_SET, PH_PREPARE, fr(OF_SPEC_SET, s, sigma, 0, 0), why); UNLOCK; return r; }
OpId op_specialize_set(SetId s, MapId sigma) { LOCK; OpId h = op_new(OF_SPEC_SET, PH_PREPARE, fr(OF_SPEC_SET, s, sigma, 0, 0)); UNLOCK; return h; }

/* SPEC_FORMULA: a = F, b = σ; memo (F, σ, env) */
static void step_spec_formula(Op *o, Frame *f) {
    FormulaId F = f->a;
    switch (f->ph) {
    case 0: {
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO || t == FM_ONE) { fin(o, F); return; }
        uint64_t k[5] = { K_MEMO, 0xF00D, F, f->b, global_env_version() }; f->ph = 1; push_lookup(o, k, 5); return;
    }
    case 1:
        if (o->ret && side(o->ret)->has_val) { W.L.memo_hit++; W.L.memo_deliver++; fin(o, side(o->ret)->val); return; }
        if (formula_tag(F) == FM_ATOM) { f->ph = 5; push(o, fr(OF_ATOMSPEC, formula_atom_of(F), f->b, 0, 0)); return; }
        f->ph = 2; push(o, fr(OF_SPEC_FORMULA, formula_left(F), f->b, 0, 0)); return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_SPEC_FORMULA, formula_right(F), f->b, 0, 0)); return;
    case 3: f->ph = 6; push(o, fr_mkf(formula_tag(F), f->acc, o->ret)); return;
    case 5: f->ph = 6; push(o, fr_mkf(FM_ATOM, o->ret, 0)); return;
    case 6: { f->acc3 = o->ret; uint64_t k[5] = { K_MEMO, 0xF00D, F, f->b, global_env_version() }; f->ph = 7; push_intern(o, k, 5); return; }
    case 7: { Side *s = side(o->ret); s->val = f->acc3; s->has_val = true; fin(o, f->acc3); return; }
    }
}
FormulaId formula_specialize(FormulaId F, MapId sigma, const char **why) { LOCK; FormulaId r = run_op(OF_SPEC_FORMULA, PH_PREPARE, fr(OF_SPEC_FORMULA, F, sigma, 0, 0), why); UNLOCK; return r; }

/* ---- families: [K_FAMILY, set ids (sorted)] ---- */
size_t family_sets(FamilyId f, const SetId **out) { size_t n; const uint64_t *w = rec_words(f, &n); require(w[0] == K_FAMILY, "not a family"); *out = w + 1; return n - 1; }
FamilyId family_zero(void) { return W.FAM0; }
FamilyId family_one(void) { return W.FAM1; }

/* NORMALIZE: buf = candidate set ids; drop duplicates and strict supersets (N). i = candidate, j = other; SUBSET children. */
static void step_normalize(Op *o, Frame *f) {
    size_t n = f->buf.n;
    switch (f->ph) {
    case 0:   /* keep flags, CHUNK_WORDS per unit (§94.2(1)) */
        if (f->buf2.n < n) { size_t end = f->buf2.n + CHUNK_WORDS; if (end > n) end = n; while (f->buf2.n < end) words_push(&f->buf2, 1); return; }
        f->i = 0; f->j = 0; f->ph = 1; return;
    case 1:
        if (f->i >= n) { f->ph = 3; f->i = 0; f->j = 0; f->acc = 0; return; }
        if (f->j >= n) { f->i++; f->j = 0; return; }
        if (f->j == f->i || !f->buf2.w[f->j] || !f->buf2.w[f->i]) { f->j++; return; }
        /* is buf[j] ⊆ buf[i]?  equal sets: keep the first (lower index) */
        if (f->buf.w[f->j] == f->buf.w[f->i]) { W.L.word_compares++; if (f->j < f->i) f->buf2.w[f->i] = 0; f->j++; return; }
        f->ph = 2; push(o, fr(OF_SUBSET, f->buf.w[f->j], f->buf.w[f->i], 0, 0)); return;
    case 2: if (o->ret == 1) f->buf2.w[f->i] = 0; f->j++; f->ph = 1; return;
    case 3: {   /* survivor compaction, CHUNK_WORDS per unit: i scans, acc writes */
        if (f->i == 0 && f->acc == 0 && f->j == 0) { f->j = 1; }
        size_t end = f->i + CHUNK_WORDS; if (end > n) end = n;
        for (; f->i < end; f->i++) if (f->buf2.w[f->i]) f->buf.w[f->acc++] = f->buf.w[f->i];
        if (f->i < n) return;
        f->buf.n = f->acc; f->ph = 4; push(o, fr_sort_own(K_FAMILY, &f->buf)); return;
    }
    case 4: fin(o, o->ret); return;
    }
}
/* FAMOP: a = 1 plus / 2 times, b = A, c = B */
static void step_famop(Op *o, Frame *f) {
    size_t na, nb; const SetId *A, *B; na = family_sets(f->b, &A); nb = family_sets(f->c, &B);
    switch (f->ph) {
    case 0:
        if (f->a == 1) { for (size_t i = 0; i < na; i++) words_push(&f->buf, A[i]); for (size_t j = 0; j < nb; j++) words_push(&f->buf, B[j]); charge(FR_ALLOCATE_CHUNK); f->ph = 3; return; }
        f->ph = 1; return;
    case 1:   /* pairwise unions */
        if (f->i >= na) { f->ph = 3; return; }
        if (f->j >= nb) { f->i++; f->j = 0; return; }
        f->ph = 2; push(o, fr(OF_SETOP, SO_UNION, A[f->i], B[f->j], 0)); return;
    case 2: words_push(&f->buf, o->ret); f->j++; f->ph = 1; return;
    case 3: { Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); words_append(&g.buf, f->buf.w, f->buf.n); f->ph = 4; push(o, g); return; }
    case 4: fin(o, o->ret); return;
    }
}
FamilyId family_make(size_t n, const SetId *sets) { LOCK; Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); words_append(&g.buf, sets, n); FamilyId r = run_op(OF_NORMALIZE, PH_REWRITE, g, NULL); UNLOCK; return r; }
FamilyId family_plus(FamilyId a, FamilyId b) { LOCK; FamilyId r = run_op(OF_FAMOP, PH_REWRITE, fr(OF_FAMOP, 1, a, b, 0), NULL); UNLOCK; return r; }
FamilyId family_times(FamilyId a, FamilyId b) { LOCK; FamilyId r = run_op(OF_FAMOP, PH_REWRITE, fr(OF_FAMOP, 2, a, b, 0), NULL); UNLOCK; return r; }
/* ANTICHAIN: a = F; memo (F) */
static void step_antichain(Op *o, Frame *f) {
    FormulaId F = f->a;
    switch (f->ph) {
    case 0: {
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO) { fin(o, W.FAM0); return; }
        if (t == FM_ONE) { fin(o, W.FAM1); return; }
        uint64_t k[3] = { K_MEMO, 0xAC, F }; f->ph = 1; push_lookup(o, k, 3); return;
    }
    case 1:
        if (o->ret && side(o->ret)->has_val) { W.L.memo_hit++; W.L.memo_deliver++; fin(o, side(o->ret)->val); return; }
        if (formula_tag(F) == FM_ATOM) { uint64_t w[2] = { K_SET, formula_atom_of(F) }; f->ph = 5; push_intern(o, w, 2); return; }
        f->ph = 2; push(o, fr(OF_ANTICHAIN, formula_left(F), 0, 0, 0)); return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_ANTICHAIN, formula_right(F), 0, 0, 0)); return;
    case 3: f->ph = 6; push(o, fr(OF_FAMOP, formula_tag(F) == FM_OR ? 1 : 2, f->acc, o->ret, 0)); return;
    case 5: { Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); words_push(&g.buf, o->ret); f->ph = 6; push(o, g); return; }
    case 6: { f->acc3 = o->ret; uint64_t k[3] = { K_MEMO, 0xAC, F }; f->ph = 7; push_intern(o, k, 3); return; }
    case 7: { Side *s = side(o->ret); s->val = f->acc3; s->has_val = true; fin(o, f->acc3); return; }
    }
}
FamilyId formula_antichain(FormulaId F) { LOCK; FamilyId r = run_op(OF_ANTICHAIN, PH_REWRITE, fr(OF_ANTICHAIN, F, 0, 0, 0), NULL); UNLOCK; return r; }
OpId op_antichain(FormulaId F) { LOCK; OpId h = op_new(OF_ANTICHAIN, PH_REWRITE, fr(OF_ANTICHAIN, F, 0, 0, 0)); UNLOCK; return h; }
static uint64_t *copy_words(const uint64_t *w, size_t n) { uint64_t *c = malloc((n ? n : 1) * sizeof(uint64_t)); require(c, "out of memory"); if (n) memcpy(c, w, n * sizeof(uint64_t)); return c; }
bool family_dominates(FamilyId a, FamilyId b) {
    LOCK; size_t na, nb; const SetId *A0, *B0; na = family_sets(a, &A0); nb = family_sets(b, &B0);
    uint64_t *A = copy_words(A0, na), *B = copy_words(B0, nb);   /* the store may move while subsets intern */
    bool ok = true;
    for (size_t j = 0; ok && j < nb; j++) { bool found = false; for (size_t i = 0; !found && i < na; i++) { charge(FR_FAMILY_CHUNK); found = subset_locked(A[i], B[j]); } ok = found; }
    free(A); free(B);
    UNLOCK; return ok;
}
Cost family_residual(FamilyId a, SetId k, ModelId m) {
    LOCK; size_t na; const SetId *A0; na = family_sets(a, &A0); uint64_t *A = copy_words(A0, na); Cost best = COST_INF;
    for (size_t i = 0; i < na; i++) { SetId d = setop(SO_DIFF, A[i], k); Cost c = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, d, m, 0, 0), NULL); W.L.limb_ops++; charge(FR_COST_COMPARE_CHUNK); if (c < best) best = c; }
    free(A);
    UNLOCK; return best;
}
FamilyId family_specialize(FamilyId a, MapId sigma, const char **why) {
    LOCK; size_t na; const SetId *A0; na = family_sets(a, &A0); uint64_t *A = copy_words(A0, na);
    uint64_t *ids = na ? malloc(na * sizeof(uint64_t)) : NULL; require(!na || ids, "out of memory");
    for (size_t i = 0; i < na; i++) { ids[i] = run_op(OF_SPEC_SET, PH_PREPARE, fr(OF_SPEC_SET, A[i], sigma, 0, 0), why); if (!ids[i]) { free(ids); free(A); UNLOCK; return 0; } }
    free(A);
    Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); words_append(&g.buf, ids, na); free(ids);
    FamilyId r = run_op(OF_NORMALIZE, PH_REWRITE, g, NULL);
    UNLOCK; return r;
}

/* ---- cost models: [K_MODEL, name, 8 kind weights, completed set, overrides list] ---- */
static Cost kind_weight(ModelId m, AtomId a) {
    size_t n; const uint64_t *w = rec_words(m, &n); require(w[0] == K_MODEL, "not a cost model");
    AtomKind k = atom_kind(a);
    return w[1 + (unsigned)k];
}
static void model_register_overrides(ModelId m) {
    uint64_t list = rec_w(m, 11); if (!list) return;
    size_t n; const uint64_t *l = rec_words(list, &n);
    for (size_t i = 1; i + 1 < n; i += 2) { uint64_t k[3] = { K_WEIGHT, m, l[i] }; uint64_t id = intern_sync(k, 3, NULL); side(id)->val = l[i + 1]; side(id)->has_val = true; }
}
ModelId model_make(uint64_t name, KindWeights kw, SetId completed) {
    LOCK; uint64_t w[12] = { K_MODEL, name, kw.producer, kw.request, kw.deliver, kw.pub, kw.eval, kw.apply, kw.slot, kw.named, completed, 0 };
    ModelId m = intern_sync(w, 12, NULL); UNLOCK; return m;
}
ModelId model_with_weight(ModelId m, AtomId a, Cost wt) {
    LOCK; size_t n; const uint64_t *w = rec_words(m, &n); uint64_t nw[12]; memcpy(nw, w, 12 * sizeof(uint64_t));
    Words l; words_init(&l); words_push(&l, K_LIST);
    if (w[11]) { size_t k; const uint64_t *old = rec_words(w[11], &k); words_append(&l, old + 1, k - 1); }
    words_push(&l, a); words_push(&l, wt);
    nw[11] = intern_sync(l.w, l.n, NULL); words_free(&l);
    ModelId r = intern_sync(nw, 12, NULL); model_register_overrides(r); UNLOCK; return r;
}
ModelId model_with_completed(ModelId m, SetId completed) { LOCK; size_t n; const uint64_t *w = rec_words(m, &n); uint64_t nw[12]; memcpy(nw, w, 12 * sizeof(uint64_t)); nw[10] = completed; ModelId r = intern_sync(nw, 12, NULL); model_register_overrides(r); UNLOCK; return r; }
static Cost weight_locked(ModelId m, AtomId a) { uint64_t k[3] = { K_WEIGHT, m, a }; W.L.memo_lookup++; uint64_t id = find_sync(k, 3); if (id && side(id)->has_val) { W.L.memo_hit++; return side(id)->val; } return kind_weight(m, a); }
Cost model_weight(ModelId m, AtomId a) { LOCK; Cost c = weight_locked(m, a); UNLOCK; return c; }
SetId model_completed(ModelId m) { return rec_w(m, 10); }

/* ---- cost differences (§63) ---- */
typedef struct { int64_t eps, masked; } CostDiffInfo;
CostDiffId costdiff_make(SetId a, SetId b, SetId k, SetId c, ModelId m) {
    LOCK;
    SetId ak = setop(SO_DIFF, a, k), bk = setop(SO_DIFF, b, k);
    Cost ca = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, ak, m, 0, 0), NULL), cb = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, bk, m, 0, 0), NULL);
    SetId akc = setop(SO_DIFF, ak, c), bkc = setop(SO_DIFF, bk, c);
    Cost ma = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, akc, m, 0, 0), NULL), mb = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, bkc, m, 0, 0), NULL);
    W.L.limb_ops += 2; charge(FR_COST_ADD_CHUNK); charge(FR_COST_ADD_CHUNK);
    uint64_t w[8] = { K_COSTDIFF, a, b, k, c, m, check_session_id(), global_env_version() };
    CostDiffId id = intern_sync(w, 8, NULL);
    if (!side(id)->ptr) { CostDiffInfo *in = own(calloc(1, sizeof *in)); require(in, "out of memory"); in->eps = (int64_t)ca - (int64_t)cb; in->masked = (int64_t)ma - (int64_t)mb; side(id)->ptr = in; }
    UNLOCK; return id;
}
int64_t costdiff_epsilon(CostDiffId d) { return ((CostDiffInfo *)side(d)->ptr)->eps; }
int64_t costdiff_masked(CostDiffId d) { return ((CostDiffInfo *)side(d)->ptr)->masked; }
bool costdiff_current(CostDiffId d) { return rec_w(d, 6) == check_session_id() && rec_w(d, 7) == global_env_version(); }

/* ---------------------------------------------------------------- 6. typed records, preparation, realization (§66–§68.3) ---- */

BoundaryId boundary_make(ContextId ctx, FaceId face, size_t ninputs, const RefId *inputs, RefId type, uint64_t level, RefId continuation) {
    const char *why; uint64_t lv = 0; W.L.kernel_calls++;
    if (check_is_type(ctx, face, type, &lv, &why) != CK_VALID || lv != level) return 0;
    LOCK; Words w; words_init(&w);
    uint64_t h[9] = { K_BOUNDARY, check_session_id(), global_env_version(), ctx, face, type, level, continuation, ninputs };
    words_append(&w, h, 9); words_append(&w, inputs, ninputs);
    BoundaryId b = intern_sync(w.w, w.n, NULL); words_free(&w); UNLOCK; return b;
}
static uint64_t list_make_locked(size_t n, const uint64_t *x) { Words w; words_init(&w); words_push(&w, K_LIST); words_append(&w, x, n); uint64_t id = intern_sync(w.w, w.n, NULL); words_free(&w); return id; }
static size_t list_get(uint64_t id, const uint64_t **out) { size_t n; const uint64_t *w = rec_words(id, &n); require(w[0] == K_LIST, "not a list"); *out = w + 1; return n - 1; }
static SetId set_of_list_locked(uint64_t list) { const uint64_t *x; size_t n = list_get(list, &x); uint64_t *c = n ? malloc(n * sizeof(uint64_t)) : NULL; require(!n || c, "out of memory"); if (n) memcpy(c, x, n * sizeof(uint64_t)); sort_counted(c, n); size_t m = 0; for (size_t i = 0; i < n; i++) if (!m || c[m - 1] != c[i]) c[m++] = c[i]; SetId s = set_intern_sorted(c, m); free(c); return s; }

PlanId plan_make(BoundaryId b, RefId r, RefId evidence, size_t nwork, const AtomId *work, const char **why) {
    size_t n; const uint64_t *bw = rec_words(b, &n); require(bw[0] == K_BOUNDARY, "not a boundary");
    ContextId ctx = bw[3]; FaceId face = bw[4]; RefId type = bw[5];
    W.L.kernel_calls++;
    if (check(ctx, face, r, type, why) != CK_VALID) return 0;
    if (evidence) { W.L.kernel_calls++; Inference q = infer(ctx, face, evidence); if (q.st != CK_VALID) { if (why) *why = q.reason ? q.reason : "connecting evidence does not type"; return 0; } }
    LOCK; uint64_t list = list_make_locked(nwork, work); SetId set = set_of_list_locked(list);
    uint64_t w[6] = { K_PLAN, b, r, evidence, set, list }; PlanId p = intern_sync(w, 6, NULL); UNLOCK; return p;
}
RefId plan_reference(PlanId p) { require(rec_kind(p) == K_PLAN, "not a plan"); return rec_w(p, 2); }
RefId plan_evidence(PlanId p) { return rec_w(p, 3); }
SetId plan_work(PlanId p) { return rec_w(p, 4); }
BoundaryId plan_boundary(PlanId p) { return rec_w(p, 1); }
ConnectorId connector_make(BoundaryId left, BoundaryId right, BoundaryId result, TransformId transform, RefId evidence, size_t nwork, const AtomId *work) {
    if (transform) require(transform_get(transform), "connector names an unknown transform");
    LOCK; uint64_t list = work ? list_make_locked(nwork, work) : 0; SetId set = work ? set_of_list_locked(list) : 0;
    uint64_t w[8] = { K_CONNECTOR, left, right, result, transform, evidence, set, list }; ConnectorId g = intern_sync(w, 8, NULL); UNLOCK; return g;
}
static ExprId expr_intern(uint64_t tag, uint64_t x, uint64_t y, uint64_t g) { LOCK; uint64_t w[5] = { K_EXPR, tag, x, y, g }; ExprId e = intern_sync(w, 5, NULL); UNLOCK; return e; }
ExprId expr_empty(BoundaryId b) { return expr_intern(EX_EMPTY, b, 0, 0); }
ExprId expr_plan(PlanId p) { return expr_intern(EX_PLAN, p, 0, 0); }
ExprId expr_alt(ExprId e, ExprId f) { return expr_intern(EX_ALT, e, f, 0); }
ExprId expr_join(ExprId e, ExprId f, ConnectorId g) { return expr_intern(EX_JOIN, e, f, g); }
ExprTag expr_tag(ExprId e) { require(rec_kind(e) == K_EXPR, "not an expression"); return (ExprTag)rec_w(e, 1); }
/* memoized per node: each expression node's boundary is computed once
 * (charged as one VALIDATE step); later calls are one bounded read */
BoundaryId expr_boundary(ExprId e) {
    Side *sd = side(e);
    if (sd->has_val) return sd->val;
    BoundaryId out = 0;
    switch (expr_tag(e)) {
    case EX_EMPTY: out = rec_w(e, 2); break;
    case EX_PLAN: out = plan_boundary(rec_w(e, 2)); break;
    case EX_ALT: { BoundaryId l = expr_boundary(rec_w(e, 2)), r = expr_boundary(rec_w(e, 3)); out = l && l == r ? l : 0; break; }
    case EX_JOIN: { BoundaryId l = expr_boundary(rec_w(e, 2)), r = expr_boundary(rec_w(e, 3)); ConnectorId g = rec_w(e, 4); if (!l || !r || !g) { out = 0; break; } out = rec_w(g, 1) == l && rec_w(g, 2) == r ? rec_w(g, 3) : 0; break; }
    }
    charge(FR_VALIDATE_PREPARED_BOUNDARY);
    sd->val = out; sd->has_val = true;
    return out;
}
PlanId plan_specialize(PlanId p, MapId sigma, ContextId target, FaceId target_face, const char **why) {
    BoundaryId b = plan_boundary(p); size_t n; const uint64_t *bw = rec_words(b, &n);
    W.L.kernel_calls++;
    if (check_map(target, target_face, sigma, bw[3], bw[4], why) != CK_VALID) return 0;
    RefId type = reindex(bw[5], sigma), cont = bw[7] ? reindex(bw[7], sigma) : 0; W.L.kernel_calls += 2;
    size_t ni = bw[8]; RefId *in = ni ? malloc(ni * sizeof(RefId)) : NULL; require(!ni || in, "out of memory");
    for (size_t i = 0; i < ni; i++) { in[i] = reindex(bw[9 + i], sigma); W.L.kernel_calls++; }
    BoundaryId nb = boundary_make(target, target_face, ni, in, type, bw[6], cont); free(in);
    if (!nb) { if (why) *why = "specialized boundary type does not form"; return 0; }
    RefId r = reindex(plan_reference(p), sigma), ev = plan_evidence(p) ? reindex(plan_evidence(p), sigma) : 0; W.L.kernel_calls += 2;
    uint64_t *lst; size_t nl; { LOCK; const uint64_t *l0; nl = list_get(rec_w(p, 5), &l0); lst = nl ? malloc(nl * sizeof(uint64_t)) : NULL; require(!nl || lst, "out of memory"); if (nl) memcpy(lst, l0, nl * sizeof(uint64_t)); UNLOCK; }   /* copied: interning below may move the store */
    SetId img = set_specialize(plan_work(p), sigma, why); if (!img) { free(lst); return 0; }
    /* the ordered list of the image keeps first occurrences in the source order */
    AtomId *ord = nl ? malloc(nl * sizeof(AtomId)) : NULL; require(!nl || ord, "out of memory"); size_t m = 0;
    for (size_t i = 0; i < nl; i++) { SetId one; { AtomId a1 = lst[i]; one = set_make(1, &a1); } SetId s1 = set_specialize(one, sigma, why); if (!s1) { free(ord); free(lst); return 0; } AtomId a = set_atoms(s1, &n)[0]; bool seen = false; for (size_t k = 0; k < m; k++) { W.L.word_compares++; if (ord[k] == a) seen = true; } if (!seen) ord[m++] = a; }
    free(lst);
    PlanId q = plan_make(nb, r, ev, m, ord, why); free(ord); return q;
}

/* §88.4: audit one evidence use at preparation; CORE/ASSUMED pass (the
 * assumptions are appended to buf3), the other outcomes fail the operation
 * with the audit's own diagnostic */
static bool audit_use(Op *o, Frame *f, ProofUse u) {
    charge(FR_PROOF_USE_AUDIT); W.L.kernel_calls++;
    switch (u.status) {
    case PU_CORE: return true;
    case PU_ASSUMED: words_append(&f->buf3, u.assumptions, u.nassumptions); return true;
    case PU_PENDING: fail(o, "proof use PENDING: connecting evidence depends on a recursive declaration component and has no logical witness yet"); return false;
    case PU_INVALID: fail(o, "proof use INVALID: connecting evidence does not type in its occurrence context"); return false;
    default: fail(o, "proof use UNRESOLVED: connecting evidence could not be checked in this session"); return false;
    }
}
static bool audit_reference_use(Op *o, Frame *f, BoundaryId b, RefId evidence) {
    size_t n; const uint64_t *bw = rec_words(b, &n); ContextId ctx = bw[3]; FaceId face = bw[4];
    W.L.kernel_calls++; Inference q = infer(ctx, face, evidence);
    if (q.st != CK_VALID) { fail(o, q.st == CK_INVALID ? "proof use INVALID: connecting evidence does not type in its occurrence context" : "proof use UNRESOLVED: connecting evidence could not be checked in this session"); return false; }
    return audit_use(o, f, proof_use(ctx, face, evidence, q.type));
}
/* PREPARE: a = expr, b = model. buf = node stack, buf2 = atom order, buf3 = hypotheses.
 * ph0 pop/validate/push children; ph7–9 atom order loop over the node's
 * ordered work list; ph2 formula; ph3 F_K; ph4 order list; ph5 problem record. */
static void step_prepare(Op *o, Frame *f) {
    switch (f->ph) {
    case 0: {
        if (f->acc == 0) { words_push(&f->buf, f->a); f->acc = 1; f->acc2 = expr_boundary(f->a); if (!f->acc2) { fail(o, "expression has no common complete boundary"); return; } }
        if (!f->buf.n) { f->ph = 2; push(o, fr(OF_EXPRF, f->a, 0, 0, 0)); return; }
        ExprId e = f->buf.w[--f->buf.n];
        f->acc3 = e; f->ph = 1; return;
    }
    case 1: {   /* VALIDATE_PREPARED_BOUNDARY */
        ExprId e = f->acc3; ExprTag t = expr_tag(e);
        if (expr_boundary(e) != f->acc2 && t != EX_JOIN) { fail(o, "alternative at a different boundary"); return; }
        f->acc4 = 0;   /* ordered atom list to scan */
        switch (t) {
        case EX_EMPTY: break;
        case EX_PLAN: {
            PlanId p = rec_w(e, 2); f->acc4 = rec_w(p, 5);
            if (plan_evidence(p) && !audit_reference_use(o, f, plan_boundary(p), plan_evidence(p))) return;
            break;
        }
        case EX_ALT: words_push(&f->buf, rec_w(e, 3)); words_push(&f->buf, rec_w(e, 2)); break;
        case EX_JOIN: {
            ConnectorId g = rec_w(e, 4); BoundaryId l = expr_boundary(rec_w(e, 2)), r = expr_boundary(rec_w(e, 3));
            if (!g) { fail(o, "composition without a connector"); return; }
            if (rec_w(g, 1) != l || rec_w(g, 2) != r) { fail(o, "incompatible composition: connector interfaces differ from the composed boundaries"); return; }
            if (rec_w(g, 3) != f->acc2 && expr_boundary(e) != f->acc2) { fail(o, "composition result at a different boundary"); return; }
            if (!rec_w(g, 4) && !rec_w(g, 5)) { fail(o, "connector without connecting evidence"); return; }
            if (!rec_w(g, 7)) { fail(o, "connector without its work set"); return; }
            if (rec_w(g, 4) && !audit_use(o, f, transform_proof_use(rec_w(g, 4)))) return;
            if (rec_w(g, 5) && !audit_reference_use(o, f, rec_w(g, 3), rec_w(g, 5))) return;
            words_push(&f->buf, rec_w(e, 3)); words_push(&f->buf, rec_w(e, 2));
            f->acc4 = rec_w(g, 7);
            break;
        }
        }
        f->i = 0; f->ph = 7; return;
    }
    case 7: {
        if (!f->acc4) { f->ph = 0; return; }
        const uint64_t *l; size_t n = list_get(f->acc4, &l);
        if (f->i >= n) { f->ph = 0; return; }
        uint64_t k[4] = { K_MARK, o->id, 4, l[f->i] }; f->ph = 8; push_lookup(o, k, 4); return;
    }
    case 8: {
        if (o->ret) { W.L.memo_hit++; f->i++; f->ph = 7; return; }
        const uint64_t *l; list_get(f->acc4, &l);
        uint64_t k[4] = { K_MARK, o->id, 4, l[f->i] }; f->ph = 9; push_intern(o, k, 4); return;
    }
    case 9: { const uint64_t *l; list_get(f->acc4, &l); words_push(&f->buf2, l[f->i]); f->i++; f->ph = 7; return; }
    case 2: f->acc3 = o->ret; f->ph = 3; push(o, fr(OF_SUBST, f->acc3, model_completed(f->b), 1, 0)); return;
    case 3: { f->acc4 = o->ret; Frame g = fr(OF_LIST, 0, 0, 0, 0); words_push(&g.buf, K_LIST); words_append(&g.buf, f->buf2.w, f->buf2.n); f->ph = 4; push(o, g); return; }
    case 4: { f->acc = o->ret; f->buf3.n = sort_unique_u64(f->buf3.w, f->buf3.n);
              Words hw; words_init(&hw); words_push(&hw, K_SET); words_append(&hw, f->buf3.w, f->buf3.n); f->buf3.n = 0;
              f->ph = 6; push_intern_own(o, &hw); return; }   /* the hypotheses set by the framed INTERN (R6) */
    case 6: { uint64_t w[10] = { K_PROBLEM, check_session_id(), global_env_version(), f->acc2, f->b, f->a, f->acc3, f->acc4, f->acc, o->ret }; f->ph = 5; push_intern(o, w, 10); return; }
    case 5: fin(o, o->ret); return;
    }
}
/* EXPRF: a = node; memo per node. PLAN: fold AND over the ordered work list; JOIN: AND of children and connector atoms. */
static void step_exprf(Op *o, Frame *f) {
    ExprId e = f->a;
    switch (f->ph) {
    case 0: { uint64_t k[3] = { K_MEMO, 0xE0, e }; f->ph = 1; push_lookup(o, k, 3); return; }
    case 1:
        if (o->ret && side(o->ret)->has_val) { W.L.memo_hit++; W.L.memo_deliver++; fin(o, side(o->ret)->val); return; }
        switch (expr_tag(e)) {
        case EX_EMPTY: f->acc = W.ZERO; f->ph = 20; return;
        case EX_PLAN: f->acc = W.ONE; f->acc4 = rec_w(rec_w(e, 2), 5); f->i = 0; f->ph = 10; return;
        case EX_ALT: case EX_JOIN: f->ph = 2; push(o, fr(OF_EXPRF, rec_w(e, 2), 0, 0, 0)); return;
        }
        return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_EXPRF, rec_w(e, 3), 0, 0, 0)); return;
    case 3: f->ph = 4; push(o, fr_mkf(expr_tag(e) == EX_ALT ? FM_OR : FM_AND, f->acc, o->ret)); return;
    case 4: f->acc = o->ret; if (expr_tag(e) == EX_JOIN) { f->acc4 = rec_w(rec_w(e, 4), 7); f->i = 0; f->ph = 10; return; } f->ph = 20; return;
    case 10: {   /* fold atoms of list acc4 into acc */
        const uint64_t *l; size_t n = list_get(f->acc4, &l);
        if (f->i >= n) { f->ph = 20; return; }
        f->ph = 11; push(o, fr_mkf(FM_ATOM, l[f->i], 0)); return;
    }
    case 11: f->ph = 12; push(o, fr_mkf(FM_AND, f->acc, o->ret)); return;
    case 12: f->acc = o->ret; f->i++; f->ph = 10; return;
    case 20: { uint64_t k[3] = { K_MEMO, 0xE0, e }; f->ph = 21; push_intern(o, k, 3); return; }
    case 21: { Side *s = side(o->ret); s->val = f->acc; s->has_val = true; fin(o, f->acc); return; }
    }
}
ProblemId problem_prepare(ExprId e, ModelId m, const char **why) { LOCK; ProblemId p = run_op(OF_PREPARE, PH_PREPARE, fr(OF_PREPARE, e, m, 0, 0), why); UNLOCK; return p; }
OpId op_prepare(ExprId e, ModelId m) { LOCK; OpId h = op_new(OF_PREPARE, PH_PREPARE, fr(OF_PREPARE, e, m, 0, 0)); UNLOCK; return h; }
FormulaId problem_formula(ProblemId p) { require(rec_kind(p) == K_PROBLEM, "not a problem"); return rec_w(p, 6); }
FormulaId problem_residual(ProblemId p) { return rec_w(p, 7); }
size_t problem_order(ProblemId p, const AtomId **out) { return list_get(rec_w(p, 8), out); }
BoundaryId problem_boundary(ProblemId p) { return rec_w(p, 3); }
ModelId problem_model(ProblemId p) { return rec_w(p, 4); }
ExprId problem_expr(ProblemId p) { return rec_w(p, 5); }
size_t problem_assumptions(ProblemId p, const uint64_t **out) { require(rec_kind(p) == K_PROBLEM, "not a problem"); size_t n; *out = set_atoms(rec_w(p, 9), &n); return n; }
bool problem_core(ProblemId p) { return set_size(rec_w(p, 9)) == 0; }
bool problem_current(ProblemId p) { return rec_w(p, 1) == check_session_id() && rec_w(p, 2) == global_env_version(); }

/* REALIZE: a = problem, b = support S. */
typedef struct { VEC(PlanId) plans; VEC(ConnectorId) conns; SetId work; Cost cost; SetId support; } Real;
static void step_realize(Op *o, Frame *f) {
    Real *R = (Real *)(uintptr_t)f->acc4;
    switch (f->ph) {
    case 0: {
        if (!R) { R = own(calloc(1, sizeof *R)); require(R, "out of memory"); f->acc4 = (uint64_t)(uintptr_t)R; R->support = f->b; }
        f->ph = 1; push(o, fr(OF_SETOP, SO_UNION, f->b, model_completed(problem_model(f->a)), 0)); return;   /* S ∪ K */
    }
    case 1: {   /* mark every available atom */
        if (!f->acc) f->acc = o->ret;
        size_t n; const AtomId *A = set_atoms(f->acc, &n);
        if (f->i < n) { uint64_t k[4] = { K_MARK, o->id, 5, A[f->i++] }; push_intern(o, k, 4); return; }
        f->ph = 2; push(o, fr(OF_REALVISIT, problem_expr(f->a), 0, 0, f->acc4)); return;
    }
    case 2:
        if (!o->ret) { fail(o, "support does not satisfy the prepared expression"); return; }
        f->acc2 = W.EMPTY; f->i = 0; f->ph = 3; return;
    case 3: {   /* W(p) = union of plan and connector work sets */
        if (f->i < R->plans.len) { f->ph = 4; push(o, fr(OF_SETOP, SO_UNION, f->acc2, plan_work(R->plans.data[f->i]), 0)); return; }
        if (f->i - R->plans.len < R->conns.len) { f->ph = 4; push(o, fr(OF_SETOP, SO_UNION, f->acc2, rec_w(R->conns.data[f->i - R->plans.len], 6), 0)); return; }
        R->work = f->acc2; f->ph = 5; push(o, fr(OF_SUBSET, R->work, f->acc, 0, 0)); return;
    }
    case 4: f->acc2 = o->ret; f->i++; f->ph = 3; return;
    case 5: if (o->ret != 1) { fail(o, "realized work is not contained in the supplied support and completed set"); return; } f->ph = 6; push(o, fr(OF_SETOP, SO_DIFF, R->work, model_completed(problem_model(f->a)), 0)); return;
    case 6: f->ph = 7; push(o, fr(OF_SUM, o->ret, problem_model(f->a), 0, 0)); return;
    case 7: { R->cost = o->ret; uint64_t w[3] = { K_REAL, f->a, f->b }; f->ph = 8; push_intern(o, w, 3); return; }
    case 8: if (!side(o->ret)->ptr) side(o->ret)->ptr = R; fin(o, o->ret); return;
    }
}
/* REALVISIT: a = node, d = Real*; result 1 satisfied / 0. On an unsatisfied subtree the appended witnesses are rolled back. */
static void step_realvisit(Op *o, Frame *f) {
    ExprId e = f->a; Real *R = (Real *)(uintptr_t)f->d;
    switch (f->ph) {
    case 0:
        f->acc = R->plans.len; f->acc2 = R->conns.len;   /* rollback marks */
        switch (expr_tag(e)) {
        case EX_EMPTY: fin(o, 0); return;
        case EX_PLAN: f->acc4 = rec_w(rec_w(e, 2), 5); f->i = 0; f->ph = 10; return;
        case EX_ALT: f->ph = 1; push(o, fr(OF_REALVISIT, rec_w(e, 2), 0, 0, f->d)); return;
        case EX_JOIN: f->ph = 3; push(o, fr(OF_REALVISIT, rec_w(e, 2), 0, 0, f->d)); return;
        }
        return;
    case 1: if (o->ret) { fin(o, 1); return; } f->ph = 2; push(o, fr(OF_REALVISIT, rec_w(e, 3), 0, 0, f->d)); return;
    case 2: fin(o, o->ret); return;
    case 3: if (!o->ret) { fin(o, 0); return; } f->ph = 4; push(o, fr(OF_REALVISIT, rec_w(e, 3), 0, 0, f->d)); return;
    case 4: if (!o->ret) { R->plans.len = f->acc; R->conns.len = f->acc2; fin(o, 0); return; } f->acc4 = rec_w(rec_w(e, 4), 7); f->i = 0; f->ph = 10; return;
    case 10: {   /* every atom of list acc4 must be available */
        const uint64_t *l; size_t n = list_get(f->acc4, &l);
        if (f->i >= n) { if (expr_tag(e) == EX_PLAN) vec_push(&R->plans, rec_w(e, 2)); else vec_push(&R->conns, rec_w(e, 4)); charge(FR_ALLOCATE_CHUNK); fin(o, 1); return; }
        uint64_t k[4] = { K_MARK, o->id, 5, l[f->i] }; f->ph = 11; push_lookup(o, k, 4); return;
    }
    case 11: if (!o->ret) { R->plans.len = f->acc; R->conns.len = f->acc2; fin(o, 0); return; } W.L.memo_hit++; f->i++; f->ph = 10; return;
    }
}
RealizationId realize(ProblemId p, SetId support, const char **why) { LOCK; RealizationId r = run_op(OF_REALIZE, PH_COMMIT, fr(OF_REALIZE, p, support, 0, 0), why); UNLOCK; return r; }
OpId op_realize(ProblemId p, SetId support) { LOCK; OpId h = op_new(OF_REALIZE, PH_COMMIT, fr(OF_REALIZE, p, support, 0, 0)); UNLOCK; return h; }
static Real *RL(RealizationId r) { require(rec_kind(r) == K_REAL, "not a realization"); return (Real *)side(r)->ptr; }
size_t realization_plans(RealizationId r, const PlanId **out) { Real *R = RL(r); *out = R->plans.data; return R->plans.len; }
size_t realization_connectors(RealizationId r, const ConnectorId **out) { Real *R = RL(r); *out = R->conns.data; return R->conns.len; }
SetId realization_work(RealizationId r) { return RL(r)->work; }
Cost realization_cost(RealizationId r) { return RL(r)->cost; }
RefId realization_reference(RealizationId r, RefId *evidence) { Real *R = RL(r); require(R->plans.len, "realization without a plan"); if (evidence) *evidence = plan_evidence(R->plans.data[0]); return plan_reference(R->plans.data[0]); }

/* ---------------------------------------------------------------- 7. proofs, certificates, the direct fragment, schemas (§69–§70) ---- */

/* proof records: [K_PROOF, rule, F, aux, c1, c2, value]; aux = atom (SPLIT), set (MANDATORY, FACTOR), list [F,G] (DISJOINT_AND, OR_BOUND), list [G, rule] (EQUAL) */
static ProofId proof_intern(ProofRule rule, FormulaId f, uint64_t aux, ProofId c1, ProofId c2, Cost value) { uint64_t w[7] = { K_PROOF, rule, f, aux, c1, c2, value }; return intern_sync(w, 7, NULL); }
static FormulaId mkf_locked(uint64_t tag, FormulaId l, FormulaId r) { return run_op(OF_MKF, W.phase, fr_mkf(tag, l, r), NULL); }
static Cost sum_locked(SetId s, ModelId m, bool *ov) { Op *o = job_sync(fr(OF_SUM, s, m, 0, 0)); uint64_t r = run_locked(o, NULL); if (ov) *ov = o->st == OP_RESOURCE_LIMIT; return o->st == OP_RESOURCE_LIMIT ? COST_MAX : r; }
static Cost cmin(Cost a, Cost b) { W.L.limb_ops++; return a < b ? a : b; }
ProofId proof_trivial(FormulaId f) { LOCK; ProofId p = proof_intern(PR_TRIVIAL, f, 0, 0, 0, 0); UNLOCK; return p; }
ProofId proof_false(void) { LOCK; ProofId p = proof_intern(PR_FALSE, W.ZERO, 0, 0, 0, COST_INF); UNLOCK; return p; }
ProofId proof_mandatory(FormulaId f, SetId m, ModelId model) { LOCK; Cost v = sum_locked(m, model, NULL); ProofId p = proof_intern(PR_MANDATORY, f, m, 0, 0, v); UNLOCK; return p; }
ProofId proof_split(FormulaId f, AtomId e, ProofId p0, ProofId p1, ModelId model) { LOCK; Cost c1; add_checked(weight_locked(model, e), rec_w(p1, 6), &c1); Cost v = cmin(rec_w(p0, 6), c1); ProofId p = proof_intern(PR_SPLIT, f, e, p0, p1, v); UNLOCK; return p; }
ProofId proof_factor(FormulaId f, SetId m, ProofId q, ModelId model) { LOCK; Cost v; add_checked(sum_locked(m, model, NULL), rec_w(q, 6), &v); ProofId p = proof_intern(PR_FACTOR, f, m, q, 0, v); UNLOCK; return p; }
ProofId proof_disjoint_and(FormulaId f, FormulaId g, ProofId p, ProofId q) { LOCK; uint64_t l[2] = { f, g }; uint64_t aux = list_make_locked(2, l); Cost v; add_checked(rec_w(p, 6), rec_w(q, 6), &v); ProofId r = proof_intern(PR_DISJOINT_AND, mkf_locked(FM_AND, f, g), aux, p, q, v); UNLOCK; return r; }
ProofId proof_or_bound(FormulaId f, FormulaId g, ProofId p, ProofId q) { LOCK; uint64_t l[2] = { f, g }; uint64_t aux = list_make_locked(2, l); Cost v = cmin(rec_w(p, 6), rec_w(q, 6)); ProofId r = proof_intern(PR_OR_BOUND, mkf_locked(FM_OR, f, g), aux, p, q, v); UNLOCK; return r; }
ProofId proof_weaken(ProofId p, Cost k) { LOCK; ProofId r = proof_intern(PR_WEAKEN, rec_w(p, 2), 0, p, 0, k); UNLOCK; return r; }
ProofId proof_equal(FormulaId f, FormulaId g, ProofId p, EqualityRule rule) { LOCK; uint64_t l[2] = { g, rule }; uint64_t aux = list_make_locked(2, l); ProofId r = proof_intern(PR_EQUAL, f, aux, p, 0, rec_w(p, 6)); UNLOCK; return r; }
ProofId proof_raw(ProofRule rule, FormulaId f, uint64_t aux, ProofId c1, ProofId c2, Cost value) { LOCK; ProofId r = proof_intern(rule, f, aux, c1, c2, value); UNLOCK; return r; }
FormulaId proof_formula(ProofId p) { require(rec_kind(p) == K_PROOF, "not a proof"); return rec_w(p, 2); }
Cost proof_value(ProofId p) { return rec_w(p, 6); }

/* the shared-choice equality (§70.3): F = (X∨Y)∧(X∨Z) with a common child X.
 * shared_or_parts finds X, Y, Z (four bounded comparisons); the image
 * X∨(Y∧Z) is then built by two framed constructor requests. */
static bool shared_or_parts(FormulaId F, FormulaId *X, FormulaId *Y, FormulaId *Z) {
    if (formula_tag(F) != FM_AND) return false;
    FormulaId A = formula_left(F), B = formula_right(F);
    if (formula_tag(A) != FM_OR || formula_tag(B) != FM_OR) return false;
    FormulaId a[2] = { formula_left(A), formula_right(A) }, b[2] = { formula_left(B), formula_right(B) };
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { W.L.word_compares++; if (a[i] == b[j]) { *X = a[i]; *Y = a[1 - i]; *Z = b[1 - j]; return true; } }
    return false;
}

/* PROOF: a = node, b = model. Verification of one supplied proof node;
 * children are verified by sub-requests (memoized per operation, cycles rejected). */
static void proof_done(Op *o, Frame *f, Cost bound) { (void)f; fin(o, bound); }
static void step_proof(Op *o, Frame *f) {
    ProofId p = f->a; ModelId model = f->b;
    size_t n; const uint64_t *w = rec_words(p, &n);
    if (w[0] != K_PROOF) { fail(o, "certificate node is not a proof record"); return; }
    ProofRule rule = (ProofRule)w[1]; FormulaId F = w[2]; uint64_t aux = w[3]; ProofId c1 = w[4], c2 = w[5]; Cost value = w[6];
    switch (f->ph) {
    case 0: reuse_bump(REUSE_PROOF_CHECK_BODY); f->ph = 2; return;   /* the verification body starts; a back-reference to a node under check is a cyclic request of its job (rejected by the engine) */
    case 2:
        switch (rule) {
        case PR_TRIVIAL: if (value != 0) { fail(o, "TRIVIAL claims a nonzero bound"); return; } proof_done(o, f, 0); return;
        case PR_FALSE: if (F != W.ZERO || value != COST_INF) { fail(o, "FALSE applies to ZERO with value INFINITY only"); return; } proof_done(o, f, COST_INF); return;
        case PR_MANDATORY: if (F == W.ZERO) { fail(o, "MANDATORY requires a nonzero formula"); return; } f->ph = 31; push(o, fr(OF_MUST, F, 0, 0, 0)); return;
        case PR_SPLIT: f->ph = 41; push(o, fr(OF_RESTRICT, F, aux, 0, 0)); return;
        case PR_FACTOR: if (F == W.ZERO) { fail(o, "FACTOR requires a nonzero formula"); return; } f->ph = 51; push(o, fr(OF_MUST, F, 0, 0, 0)); return;
        case PR_DISJOINT_AND: case PR_OR_BOUND: {
            const uint64_t *l; if (rec_kind(aux) != K_LIST || list_get(aux, &l) != 2) { fail(o, "malformed binary rule"); return; }
            f->ph = rule == PR_DISJOINT_AND ? 61 : 71; push(o, fr_mkf(rule == PR_DISJOINT_AND ? FM_AND : FM_OR, l[0], l[1])); return;
        }
        case PR_WEAKEN: if (!c1 || proof_formula(c1) != F) { fail(o, "WEAKEN child proves a different formula"); return; } f->ph = 81; push(o, fr(OF_PROOF, c1, model, 0, 0)); return;
        case PR_EQUAL: {
            const uint64_t *l; if (rec_kind(aux) != K_LIST || list_get(aux, &l) != 2) { fail(o, "malformed EQUAL node"); return; }
            FormulaId G = l[0]; if (l[1] != EQ_SHARED_OR) { fail(o, "unknown equality rule"); return; }
            FormulaId X, Y, Z;
            if (!shared_or_parts(F, &X, &Y, &Z)) { fail(o, "equality premise fails: the formula is not (X∨Y)∧(X∨Z)"); return; }
            if (!c1 || proof_formula(c1) != G) { fail(o, "EQUAL child proves a different formula"); return; }
            f->acc = X; f->ph = 92; push(o, fr_mkf(FM_AND, Y, Z)); return;
        }
        default: fail(o, "unknown proof rule"); return;
        }
    /* MANDATORY */
    case 31: if (o->ret != aux) { fail(o, "MANDATORY set is not Must(F)"); return; } f->ph = 32; push(o, fr(OF_SUM, aux, model, 0, 0)); return;
    case 32: if (o->ret != value) { fail(o, "MANDATORY value is not the weight of Must(F)"); return; } proof_done(o, f, value); return;
    /* SPLIT */
    case 41: if (!c1 || o->ret != proof_formula(c1)) { fail(o, "SPLIT: wrong cofactor at e := 0"); return; } f->ph = 42; push(o, fr(OF_RESTRICT, F, aux, 1, 0)); return;
    case 42: if (!c2 || o->ret != proof_formula(c2)) { fail(o, "SPLIT: wrong cofactor at e := 1"); return; } f->ph = 43; push(o, fr(OF_PROOF, c1, model, 0, 0)); return;
    case 43: f->acc = o->ret; f->ph = 44; push(o, fr(OF_PROOF, c2, model, 0, 0)); return;
    case 44: {
        Cost l1 = o->ret, wc; if (!add_checked(weight_locked(model, aux), l1, &wc)) { limit(o, "cost sum not representable"); return; }
        charge(FR_COST_COMPARE_CHUNK); Cost v = cmin(f->acc, wc);
        if (v != value) { fail(o, "SPLIT value is not the minimum of its branches"); return; }
        proof_done(o, f, v); return;
    }
    /* FACTOR */
    case 51: if (o->ret != aux) { fail(o, "FACTOR set is not Must(F)"); return; } f->ph = 52; push(o, fr(OF_SUBST, F, aux, 1, 0)); return;
    case 52: if (!c1 || o->ret != proof_formula(c1)) { fail(o, "FACTOR child does not concern F[M := 1]"); return; } f->ph = 53; push(o, fr(OF_PROOF, c1, model, 0, 0)); return;
    case 53: f->acc = o->ret; f->ph = 54; push(o, fr(OF_SUM, aux, model, 0, 0)); return;
    case 54: { Cost v; if (!add_checked(o->ret, f->acc, &v)) { limit(o, "cost sum not representable"); return; } if (v != value) { fail(o, "FACTOR value is not weight(M) + residual bound"); return; } proof_done(o, f, v); return; }
    /* DISJOINT_AND */
    case 61: { const uint64_t *l; list_get(aux, &l); if (o->ret != F) { fail(o, "DISJOINT_AND node formula is not the conjunction of its parts"); return; } if (!c1 || !c2 || proof_formula(c1) != l[0] || proof_formula(c2) != l[1]) { fail(o, "DISJOINT_AND children prove other formulas"); return; } f->ph = 62; push(o, fr(OF_SUPPORT, l[0], 0, 0, 0)); return; }
    case 62: { const uint64_t *l; list_get(aux, &l); f->acc = o->ret; f->ph = 63; push(o, fr(OF_SUPPORT, l[1], 0, 0, 0)); return; }
    case 63: f->ph = 64; push(o, fr(OF_SETOP, SO_INTER, f->acc, o->ret, 0)); return;
    case 64: if (o->ret != W.EMPTY) { fail(o, "DISJOINT_AND: supports are not disjoint"); return; } f->ph = 65; push(o, fr(OF_PROOF, c1, model, 0, 0)); return;
    case 65: f->acc = o->ret; f->ph = 66; push(o, fr(OF_PROOF, c2, model, 0, 0)); return;
    case 66: { Cost v; if (!add_checked(f->acc, o->ret, &v)) { limit(o, "cost sum not representable"); return; } if (v != value) { fail(o, "DISJOINT_AND value is not the sum of its parts"); return; } proof_done(o, f, v); return; }
    /* OR_BOUND */
    case 71: { const uint64_t *l; list_get(aux, &l); if (o->ret != F) { fail(o, "OR_BOUND node formula is not the disjunction of its parts"); return; } if (!c1 || !c2 || proof_formula(c1) != l[0] || proof_formula(c2) != l[1]) { fail(o, "OR_BOUND children prove other formulas"); return; } f->ph = 72; push(o, fr(OF_PROOF, c1, model, 0, 0)); return; }
    case 72: f->acc = o->ret; f->ph = 73; push(o, fr(OF_PROOF, c2, model, 0, 0)); return;
    case 73: { charge(FR_COST_COMPARE_CHUNK); Cost v = cmin(f->acc, o->ret); if (v != value) { fail(o, "OR_BOUND value is not the minimum of its parts"); return; } proof_done(o, f, v); return; }
    /* WEAKEN */
    case 81: { charge(FR_COST_COMPARE_CHUNK); W.L.limb_ops++; if (value > o->ret) { fail(o, "WEAKEN claims more than its child"); return; } proof_done(o, f, value); return; }
    /* EQUAL */
    case 92: f->ph = 93; push(o, fr_mkf(FM_OR, f->acc, o->ret)); return;
    case 93: { const uint64_t *l; list_get(aux, &l); if (o->ret != l[0]) { fail(o, "equality premise fails: the image is not X∨(Y∧Z)"); return; } f->ph = 91; push(o, fr(OF_PROOF, c1, model, 0, 0)); return; }
    case 91: if (o->ret != value) { fail(o, "EQUAL value differs from its child"); return; } proof_done(o, f, value); return;
    }
}

/* certificates: [K_CERT, problem, lower, upper, L, U] */
CertId certificate_make(ProblemId p, ProofId lower, RealizationId upper, Cost l, Cost u) { LOCK; uint64_t w[6] = { K_CERT, p, lower, upper, l, u }; CertId c = intern_sync(w, 6, NULL); UNLOCK; return c; }
CertId certificate_problem_of(CertId c) { require(rec_kind(c) == K_CERT, "not a certificate"); return rec_w(c, 1); }
/* CHECKCERT: a = problem, b = cert. Result 1 = optimum certified, 2 = emptiness certified. */
static void step_checkcert(Op *o, Frame *f) {
    ProblemId p = f->a; size_t n; const uint64_t *c = rec_words(f->b, &n);
    if (c[0] != K_CERT) { fail(o, "not a certificate"); return; }
    ProofId lower = c[2]; RealizationId upper = c[3]; Cost L = c[4], U = c[5];
    switch (f->ph) {
    case 0:
        if (c[1] != p) { fail(o, "certificate was issued for a different prepared problem (boundary, family, resource model or snapshot differ)"); return; }
        if (!problem_current(p)) { fail(o, "stale premises: the environment or session changed since preparation"); return; }
        if (!lower || rec_kind(lower) != K_PROOF || proof_formula(lower) != problem_residual(p)) { fail(o, "root formula does not represent the prepared problem"); return; }
        f->ph = 1; push(o, fr(OF_PROOF, lower, problem_model(p), 0, 0)); return;
    case 1:
        if (o->ret != L) { fail(o, "claimed lower bound differs from the verified bound"); return; }
        if (!upper) { if (L != COST_INF) { fail(o, "no upper witness: not an optimality certificate"); return; } fin(o, 2); return; }
        if (rec_kind(upper) != K_REAL || rec_w(upper, 1) != p) { fail(o, "upper witness belongs to a different problem"); return; }
        f->ph = 2; push(o, fr(OF_REALIZE, p, rec_w(upper, 2), 0, 0)); return;   /* reconstruct from the witness's support */
    case 2: {
        Real *a = RL(o->ret), *b = RL(upper);
        if (a->cost != U || b->cost != U || a->work != b->work) { fail(o, "upper witness does not attain the claimed value"); return; }
        charge(FR_COST_COMPARE_CHUNK); W.L.limb_ops++;
        if (L != U || L == COST_INF) { fail(o, "lower bound below the witness: not an optimality certificate"); return; }
        fin(o, 1); return;
    }
    }
}
CertStatus certificate_check(ProblemId p, CertId c, const char **why) {
    LOCK; Op *o = job_sync(fr(OF_CHECKCERT, p, c, 0, 0));
    run_locked(o, why); CertStatus s = o->st == OP_COMPLETE ? CERT_VALID : o->st == OP_RESOURCE_LIMIT ? CERT_UNRESOLVED : CERT_INVALID;
    if (o->st != OP_COMPLETE && why) *why = o->diag;
    UNLOCK; return s;
}
OpId op_check_certificate(ProblemId p, CertId c) { LOCK; OpId h = op_new(OF_CHECKCERT, PH_CHECK, fr(OF_CHECKCERT, p, c, 0, 0)); UNLOCK; return h; }

/* REDUCE: a = F, b = model. Bottom-up; each rule fires only when its checked
 * premise holds; otherwise the formula is retained unreduced. Result: a
 * reduction record whose side struct is the Reduction. */
typedef struct { Reduction r; } RedRec;
/* §75.3: the answer is identified by (formula, model, rule set); it holds the
 * reduced flag, bound, proof and attaining support */
/* R6: the reduction's records are interned by framed INTERN children, one
 * per record (aux list, proof, reduction), never synchronously inside a unit.
 * The finishing data is retained in the frame: acc = value, acc2 = attaining,
 * acc3 = proof rule (or the interned proof once built), i/j = aux words,
 * c/d = child proofs, e = flags (1 reduced, 2 aux is a two-element list). */
static void reduce_finish(Op *o, Frame *f, bool reduced, Cost value, SetId attaining, ProofRule rule, bool aux_list, uint64_t aux0, uint64_t aux1, ProofId c1, ProofId c2) {
    (void)o;
    f->acc = value; f->acc2 = attaining; f->acc3 = rule; f->i = aux0; f->j = aux1; f->c = c1; f->d = c2;
    f->e = (reduced ? 1u : 0u) | (aux_list ? 2u : 0u);
    f->ph = 90;
}
static Reduction *RED(uint64_t id) { return &((RedRec *)side(id)->ptr)->r; }
static void step_reduce(Op *o, Frame *f) {
    FormulaId F = f->a; ModelId model = f->b;
    switch (f->ph) {
    /* ---- the framed finish (R6) ---- */
    case 90: if (f->e & 2) { uint64_t w[3] = { K_LIST, f->i, f->j }; f->ph = 91; push_intern(o, w, 3); return; } f->ph = 92; return;
    case 91: f->i = o->ret; f->ph = 92; return;
    case 92: if (f->e & 1) { uint64_t w[7] = { K_PROOF, f->acc3, F, f->i, f->c, f->d, f->acc }; f->ph = 93; push_intern(o, w, 7); return; } f->acc3 = 0; f->ph = 94; return;
    case 93: f->acc3 = o->ret; f->ph = 94; return;
    case 94: { uint64_t w[4] = { K_REDUCTION, F, model, RULES_VERSION }; f->ph = 95; push_intern(o, w, 4); return; }
    case 95: {
        uint64_t id = o->ret;
        if (!side(id)->ptr) { RedRec *rr = own(calloc(1, sizeof *rr)); require(rr, "out of memory"); rr->r.formula = F; rr->r.reduced = (f->e & 1) != 0; rr->r.value = f->acc; rr->r.lower = f->acc3; rr->r.attaining = f->acc2; side(id)->ptr = rr; }
        fin(o, id); return;
    }
    case 0: reuse_bump(REUSE_REDUCE_BODY); f->ph = 1; return;   /* the body starts: the persistent job is the memo (§75.3) */
    case 1:
        switch (formula_tag(F)) {
        case FM_ZERO: reduce_finish(o, f, true, COST_INF, 0, PR_FALSE, false, 0, 0, 0, 0); return;
        case FM_ONE: reduce_finish(o, f, true, 0, W.EMPTY, PR_TRIVIAL, false, 0, 0, 0, 0); return;
        case FM_ATOM: { uint64_t w[2] = { K_SET, formula_atom_of(F) }; f->ph = 2; push_intern(o, w, 2); return; }
        case FM_OR: f->ph = 10; push(o, fr(OF_REDUCE, formula_left(F), model, 0, 0)); return;
        case FM_AND: f->ph = 20; push(o, fr(OF_SUPPORT, formula_left(F), 0, 0, 0)); return;
        }
        return;
    case 2: { f->acc = o->ret; f->ph = 3; push(o, fr(OF_SUM, f->acc, model, 0, 0)); return; }
    case 3: reduce_finish(o, f, true, o->ret, f->acc, PR_MANDATORY, false, f->acc, 0, 0, 0); return;
    /* OR */
    case 10: f->acc = o->ret; f->ph = 11; push(o, fr(OF_REDUCE, formula_right(F), model, 0, 0)); return;
    case 11: {
        Reduction *l = RED(f->acc), *rg = RED(o->ret);
        if (!l->reduced || !rg->reduced) { reduce_finish(o, f, false, 0, 0, 0, false, 0, 0, 0, 0); return; }
        charge(FR_COST_COMPARE_CHUNK); Cost v = cmin(l->value, rg->value);
        reduce_finish(o, f, true, v, l->value <= rg->value ? l->attaining : rg->attaining, PR_OR_BOUND, true, formula_left(F), formula_right(F), l->lower, rg->lower); return;
    }
    /* AND */
    case 20: f->acc = o->ret; f->ph = 21; push(o, fr(OF_SUPPORT, formula_right(F), 0, 0, 0)); return;
    case 21: f->acc2 = o->ret; f->ph = 22; push(o, fr(OF_SETOP, SO_INTER, f->acc, f->acc2, 0)); return;
    case 22:
        if (o->ret == W.EMPTY) { f->ph = 23; push(o, fr(OF_REDUCE, formula_left(F), model, 0, 0)); return; }
        f->ph = 30; push(o, fr(OF_MUST, F, 0, 0, 0)); return;
    case 23: f->acc3 = o->ret; f->ph = 24; push(o, fr(OF_REDUCE, formula_right(F), model, 0, 0)); return;
    case 24: {
        Reduction *l = RED(f->acc3), *rg = RED(o->ret);
        if (!l->reduced || !rg->reduced) { reduce_finish(o, f, false, 0, 0, 0, false, 0, 0, 0, 0); return; }
        Cost v; if (!add_checked(l->value, rg->value, &v)) { limit(o, "cost sum not representable"); return; }
        f->acc4 = o->ret; f->acc = v;
        if (l->attaining && rg->attaining) { f->ph = 25; push(o, fr(OF_SETOP, SO_UNION, l->attaining, rg->attaining, 0)); return; }
        reduce_finish(o, f, true, v, 0, PR_DISJOINT_AND, true, formula_left(F), formula_right(F), l->lower, rg->lower); return;
    }
    case 25: {
        Reduction *l = RED(f->acc3), *rg = RED(f->acc4);
        reduce_finish(o, f, true, f->acc, o->ret, PR_DISJOINT_AND, true, formula_left(F), formula_right(F), l->lower, rg->lower); return;
    }
    case 30: {   /* Must(F) */
        f->acc = o->ret;
        if (f->acc != W.EMPTY) { f->ph = 31; push(o, fr(OF_SUBST, F, f->acc, 1, 0)); return; }
        FormulaId X, Y, Z;
        if (!shared_or_parts(F, &X, &Y, &Z)) { reduce_finish(o, f, false, 0, 0, 0, false, 0, 0, 0, 0); return; }
        f->acc3 = X; f->ph = 38; push(o, fr_mkf(FM_AND, Y, Z)); return;
    }
    case 38: f->ph = 39; push(o, fr_mkf(FM_OR, f->acc3, o->ret)); return;
    case 39: f->acc2 = o->ret; f->ph = 40; push(o, fr(OF_REDUCE, f->acc2, model, 0, 0)); return;
    case 31: f->acc2 = o->ret; f->ph = 32; push(o, fr(OF_REDUCE, f->acc2, model, 0, 0)); return;
    case 32: {
        Reduction *g = RED(o->ret);
        if (!g->reduced) { reduce_finish(o, f, false, 0, 0, 0, false, 0, 0, 0, 0); return; }
        f->acc3 = o->ret; f->ph = 33; push(o, fr(OF_SUM, f->acc, model, 0, 0)); return;
    }
    case 33: {
        Reduction *g = RED(f->acc3); Cost v; if (!add_checked(o->ret, g->value, &v)) { limit(o, "cost sum not representable"); return; }
        f->acc4 = v;
        if (g->attaining) { f->ph = 34; push(o, fr(OF_SETOP, SO_UNION, f->acc, g->attaining, 0)); return; }
        reduce_finish(o, f, true, v, 0, PR_FACTOR, false, f->acc, 0, g->lower, 0); return;
    }
    case 34: { Reduction *g = RED(f->acc3); reduce_finish(o, f, true, f->acc4, o->ret, PR_FACTOR, false, f->acc, 0, g->lower, 0); return; }
    case 40: {
        Reduction *g = RED(o->ret);
        if (!g->reduced) { reduce_finish(o, f, false, 0, 0, 0, false, 0, 0, 0, 0); return; }
        reduce_finish(o, f, true, g->value, g->attaining, PR_EQUAL, true, f->acc2, EQ_SHARED_OR, g->lower, 0); return;
    }
    }
}
Reduction formula_reduce(FormulaId F, ModelId m, const char **why) {
    LOCK; Reduction out; memset(&out, 0, sizeof out);
    uint64_t id = run_op(OF_REDUCE, PH_REWRITE, fr(OF_REDUCE, F, m, 0, 0), why);
    if (id) out = *RED(id);
    UNLOCK; return out;
}
OpId op_reduce(FormulaId F, ModelId m) { LOCK; OpId h = op_new(OF_REDUCE, PH_REWRITE, fr(OF_REDUCE, F, m, 0, 0)); UNLOCK; return h; }
CertId problem_reduce(ProblemId p, const char **why) {
    Reduction r = formula_reduce(problem_residual(p), problem_model(p), why);
    if (!r.reduced) { if (why) *why = "formula retained unreduced: no direct rule applies"; return 0; }
    if (r.value == COST_INF) return certificate_make(p, r.lower, 0, COST_INF, COST_INF);
    RealizationId real = realize(p, r.attaining, why); if (!real) return 0;
    return certificate_make(p, r.lower, real, r.value, realization_cost(real));
}

/* ---- schemas (§70.4): [K_SCHEMA, nslots, formula, lower, attaining]; atom maps [K_AMAP, n, from..., to...] ---- */
SchemaId schema_make(size_t nslots, FormulaId formula, ProofId lower, SetId attaining) { LOCK; uint64_t w[5] = { K_SCHEMA, nslots, formula, lower, attaining }; SchemaId s = intern_sync(w, 5, NULL); UNLOCK; return s; }
AtomMapId atom_map_make(size_t n, const AtomId *from, const AtomId *to) {
    LOCK; Words w; words_init(&w); words_push(&w, K_AMAP); words_push(&w, n); words_append(&w, from, n); words_append(&w, to, n); AtomMapId m = intern_sync(w.w, w.n, NULL); words_free(&w);
    for (size_t i = 0; i < n; i++) { uint64_t e[4] = { K_MEMO, 0xA3, m, from[i] }; uint64_t id = intern_sync(e, 4, NULL); side(id)->val = to[i]; side(id)->has_val = true; }   /* one entry record per slot: a fixed-size probe at use */
    UNLOCK; return m;
}
static AtomId amap_apply(AtomMapId m, AtomId a) { uint64_t e[4] = { K_MEMO, 0xA3, m, a }; uint64_t id = find_sync(e, 4); return id && side(id)->has_val ? side(id)->val : a; }
/* MAPF: a = F, b = map; memo (F, map) */
static void step_mapf(Op *o, Frame *f) {
    FormulaId F = f->a;
    switch (f->ph) {
    case 0: {
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO || t == FM_ONE) { fin(o, F); return; }
        if (t == FM_ATOM) { f->ph = 5; push(o, fr_mkf(FM_ATOM, amap_apply(f->b, formula_atom_of(F)), 0)); return; }
        uint64_t k[4] = { K_MEMO, 0xA1, F, f->b }; f->ph = 1; push_lookup(o, k, 4); return;
    }
    case 1:
        if (o->ret && side(o->ret)->has_val) { W.L.memo_hit++; W.L.memo_deliver++; fin(o, side(o->ret)->val); return; }
        f->ph = 2; push(o, fr(OF_MAPF, formula_left(F), f->b, 0, 0)); return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_MAPF, formula_right(F), f->b, 0, 0)); return;
    case 3: f->ph = 4; push(o, fr_mkf(formula_tag(F), f->acc, o->ret)); return;
    case 4: { f->acc3 = o->ret; uint64_t k[4] = { K_MEMO, 0xA1, F, f->b }; f->ph = 6; push_intern(o, k, 4); return; }
    case 5: fin(o, o->ret); return;
    case 6: { Side *s = side(o->ret); s->val = f->acc3; s->has_val = true; fin(o, f->acc3); return; }
    }
}
/* MAPSET: a = set, b = map: direct image */
static void step_mapset(Op *o, Frame *f) {
    size_t n; const AtomId *S = set_atoms(f->a, &n);
    if (f->ph == 0) { if (f->i < n) { words_push(&f->buf, amap_apply(f->b, S[f->i++])); return; } f->ph = 1; push(o, fr_sort_own(K_SET, &f->buf)); return; }
    fin(o, o->ret);
}
/* MAPP: a = proof, b = map, c = model: rebuild the proof node over the mapped formulas/sets with recomputed values */
/* R6: the mapped proof's records (aux list, proof) are interned by framed
 * children; the finishing data lives in the frame as for REDUCE (acc3 = rule
 * → proof, acc4 = mapped formula, i/j = aux words, buf3 = child proofs) */
static void mapp_finish(Op *o, Frame *f, ProofRule rule, FormulaId formula, bool aux_list, uint64_t aux0, uint64_t aux1, ProofId c1, ProofId c2, Cost value) {
    (void)o; f->acc3 = rule; f->acc4 = formula; f->i = aux0; f->j = aux1; f->acc = value; f->e = aux_list ? 2u : 0u;
    f->buf3.n = 0; words_push(&f->buf3, c1); words_push(&f->buf3, c2);
    f->ph = 90;
}
static void step_mapp(Op *o, Frame *f) {
    size_t n; const uint64_t *w = rec_words(f->a, &n); ProofRule rule = (ProofRule)w[1]; uint64_t aux = w[3]; ProofId c1 = w[4], c2 = w[5];
    switch (f->ph) {
    case 90: if (f->e & 2) { uint64_t lw[3] = { K_LIST, f->i, f->j }; f->ph = 91; push_intern(o, lw, 3); return; } f->ph = 92; return;
    case 91: f->i = o->ret; f->ph = 92; return;
    case 92: { uint64_t pw[7] = { K_PROOF, f->acc3, f->acc4, f->i, f->buf3.w[0], f->buf3.w[1], f->acc }; f->ph = 93; push_intern(o, pw, 7); return; }
    case 93: fin(o, o->ret); return;
    case 0: f->ph = 1; push(o, fr(OF_MAPF, w[2], f->b, 0, 0)); return;
    case 1:
        f->acc = o->ret;   /* mapped F */
        switch (rule) {
        case PR_TRIVIAL: mapp_finish(o, f, PR_TRIVIAL, f->acc, false, 0, 0, 0, 0, 0); return;
        case PR_FALSE: mapp_finish(o, f, PR_FALSE, W.ZERO, false, 0, 0, 0, 0, COST_INF); return;
        case PR_MANDATORY: case PR_FACTOR: f->ph = 2; push(o, fr(OF_MAPSET, aux, f->b, 0, 0)); return;
        case PR_SPLIT: f->acc2 = amap_apply(f->b, aux); f->ph = 4; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
        case PR_DISJOINT_AND: case PR_OR_BOUND: { const uint64_t *l; list_get(aux, &l); f->ph = 6; push(o, fr(OF_MAPF, l[0], f->b, 0, 0)); return; }
        case PR_WEAKEN: f->ph = 10; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
        case PR_EQUAL: { const uint64_t *l; list_get(aux, &l); f->ph = 11; push(o, fr(OF_MAPF, l[0], f->b, 0, 0)); return; }
        default: fail(o, "unknown proof rule"); return;
        }
    case 2: f->acc2 = o->ret; f->ph = rule == PR_MANDATORY ? 13 : 3; push(o, fr(OF_SUM, f->acc2, f->c, 0, 0)); return;
    case 13: mapp_finish(o, f, PR_MANDATORY, f->acc, false, f->acc2, 0, 0, 0, o->ret); return;
    case 3: f->acc3 = o->ret; f->ph = 14; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
    case 14: { Cost v; add_checked(f->acc3, rec_w(o->ret, 6), &v); mapp_finish(o, f, PR_FACTOR, f->acc, false, f->acc2, 0, o->ret, 0, v); return; }
    case 4: f->acc3 = o->ret; f->ph = 5; push(o, fr(OF_MAPP, c2, f->b, f->c, 0)); return;
    case 5: { Cost wc; add_checked(weight_locked(f->c, f->acc2), rec_w(o->ret, 6), &wc); Cost v = cmin(rec_w(f->acc3, 6), wc); mapp_finish(o, f, PR_SPLIT, f->acc, false, f->acc2, 0, f->acc3, o->ret, v); return; }
    case 6: { const uint64_t *l; list_get(aux, &l); f->acc2 = o->ret; f->ph = 7; push(o, fr(OF_MAPF, l[1], f->b, 0, 0)); return; }
    case 7: f->acc3 = o->ret; f->ph = 8; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
    case 8: f->acc4 = o->ret; f->ph = 9; push(o, fr(OF_MAPP, c2, f->b, f->c, 0)); return;
    case 9: {   /* the mapped formula by the framed MKF, then the framed finish */
        f->acc = o->ret;   /* second mapped child proof (the mapped F in acc is no longer needed) */
        f->ph = 15; push(o, fr_mkf(rule == PR_DISJOINT_AND ? FM_AND : FM_OR, f->acc2, f->acc3)); return;
    }
    case 15: {
        Cost v; if (rule == PR_DISJOINT_AND) add_checked(rec_w(f->acc4, 6), rec_w(f->acc, 6), &v); else v = cmin(rec_w(f->acc4, 6), rec_w(f->acc, 6));
        mapp_finish(o, f, rule, o->ret, true, f->acc2, f->acc3, f->acc4, f->acc, v); return;
    }
    case 10: mapp_finish(o, f, PR_WEAKEN, f->acc, false, 0, 0, o->ret, 0, w[6]); return;
    case 11: f->acc2 = o->ret; f->ph = 12; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
    case 12: { const uint64_t *l; list_get(aux, &l); mapp_finish(o, f, PR_EQUAL, f->acc, true, f->acc2, l[1], o->ret, 0, rec_w(o->ret, 6)); return; }
    }
}
FormulaId formula_map_atoms(FormulaId f, AtomMapId map) { LOCK; FormulaId r = run_op(OF_MAPF, PH_PREPARE, fr(OF_MAPF, f, map, 0, 0), NULL); UNLOCK; return r; }
CertId schema_instantiate(SchemaId s, AtomMapId map, ProblemId p, const char **why) {
    require(rec_kind(s) == K_SCHEMA, "not a schema");
    FormulaId F = formula_map_atoms(rec_w(s, 2), map);
    if (F != problem_residual(p)) { if (why) *why = "schema instance does not match the prepared problem's formula"; return 0; }
    LOCK; ProofId lower = run_op(OF_MAPP, PH_PREPARE, fr(OF_MAPP, rec_w(s, 3), map, problem_model(p), 0), why);
    SetId att = lower ? run_op(OF_MAPSET, PH_PREPARE, fr(OF_MAPSET, rec_w(s, 4), map, 0, 0), why) : 0; UNLOCK;
    if (!lower || !att) return 0;
    RealizationId real = realize(p, att, why); if (!real) return 0;
    CertId c = certificate_make(p, lower, real, proof_value(lower), realization_cost(real));
    if (certificate_check(p, c, why) != CERT_VALID) return 0;
    return c;
}

/* ---------------------------------------------------------------- 8. geodesic certificates (§64.3) ---- */
typedef struct { uint64_t from, to; Cost c; } GEdge;
struct Geo { size_t n; VEC(GEdge) edges; Cost *V; bool *terminal; uint64_t *policy; uint64_t *rank; bool *has_rank; uint64_t rev; };
static uint64_t geo_rev(const Geo *g) { return g->rev; }
static Geo *GEO(GeoId g) { require(rec_kind(g) == K_GEO, "not a geodesic certificate"); return (Geo *)side(g)->ptr; }
GeoId geo_new(size_t nstates) {
    LOCK; static uint64_t seq; uint64_t w[3] = { K_GEO, nstates, ++seq }; GeoId g = intern_sync(w, 3, NULL);
    Geo *x = own(calloc(1, sizeof *x)); require(x, "out of memory"); x->n = nstates;
    x->V = own(calloc(nstates, sizeof(Cost))); x->terminal = own(calloc(nstates, 1)); x->policy = own(calloc(nstates, sizeof(uint64_t))); x->rank = own(calloc(nstates, sizeof(uint64_t))); x->has_rank = own(calloc(nstates, 1));
    for (size_t i = 0; i < nstates; i++) x->V[i] = COST_INF;
    side(g)->ptr = x; charge(FR_ALLOCATE_CHUNK); UNLOCK; return g;
}
void geo_terminal(GeoId g, uint64_t s) { Geo *x = GEO(g); x->terminal[s] = true; x->rev++; }
uint64_t geo_edge(GeoId g, uint64_t from, uint64_t to, Cost c) { LOCK; Geo *x = GEO(g); GEdge e = { from, to, c }; vec_push(&x->edges, e); x->rev++; charge(FR_ALLOCATE_CHUNK); UNLOCK; return x->edges.len - 1; }
void geo_value(GeoId g, uint64_t s, Cost v) { Geo *x = GEO(g); x->V[s] = v; x->rev++; }
void geo_policy(GeoId g, uint64_t s, uint64_t edge) { Geo *x = GEO(g); x->policy[s] = edge + 1; x->rev++; }
void geo_rank(GeoId g, uint64_t s, uint64_t r) { Geo *x = GEO(g); x->rank[s] = r; x->has_rank[s] = true; x->rev++; }
/* GEO: a = geo, b = root. ph0 every edge V(s) ≤ c + V(s'); ph1 every state: terminal V = 0; nonterminal with finite V: an attaining admitted step with progress */
static void step_geo(Op *o, Frame *f) {
    Geo *x = GEO(f->a);
    switch (f->ph) {
    case 0: {
        if (f->i >= x->edges.len) { f->i = 0; f->ph = 1; return; }
        GEdge e = x->edges.data[f->i++];
        if (e.from >= x->n || e.to >= x->n) { fail(o, "edge outside the stated state domain"); return; }
        Cost rhs; if (!add_checked(e.c, x->V[e.to], &rhs)) { limit(o, "cost sum not representable"); return; }
        charge(FR_COST_COMPARE_CHUNK); W.L.limb_ops++;
        if (x->V[e.from] > rhs) { fail(o, "lower-bound inequality V(s) <= c + V(s') fails on an admitted edge"); return; }
        return;
    }
    case 1: {
        if (f->i >= x->n) { fin(o, x->V[f->b]); return; }
        uint64_t s = f->i++;
        if (x->terminal[s]) { if (x->V[s] != 0) { fail(o, "a successful terminal must have V = 0"); return; } return; }
        if (x->V[s] == COST_INF) return;   /* outside the attaining policy's domain */
        if (!x->policy[s]) { fail(o, "no attaining step at a nonterminal state of the domain"); return; }
        GEdge e = x->edges.data[x->policy[s] - 1];
        if (e.from != s) { fail(o, "selected step does not start at its state"); return; }
        Cost rhs; add_checked(e.c, x->V[e.to], &rhs); charge(FR_COST_COMPARE_CHUNK); W.L.limb_ops++;
        if (x->V[s] != rhs) { fail(o, "selected step does not attain V(s) = c + V(s')"); return; }
        if (e.c == 0 && !(x->has_rank[s] && x->has_rank[e.to] && x->rank[s] > x->rank[e.to])) { fail(o, "no progress evidence on a selected zero-cost step"); return; }
        return;
    }
    }
}
CertStatus geo_check(GeoId g, uint64_t root, Cost *value, const char **why) {
    LOCK; Op *o = job_sync(fr(OF_GEO, g, root, 0, 0));
    uint64_t v = run_locked(o, why); CertStatus s = o->st == OP_COMPLETE ? CERT_VALID : o->st == OP_RESOURCE_LIMIT ? CERT_UNRESOLVED : CERT_INVALID;
    if (o->st != OP_COMPLETE && why) *why = o->diag;
    if (value && s == CERT_VALID) *value = v;
    UNLOCK; return s;
}
OpId op_geo_check(GeoId g, uint64_t root) { LOCK; OpId h = op_new(OF_GEO, PH_CHECK, fr(OF_GEO, g, root, 0, 0)); UNLOCK; return h; }

/* ---------------------------------------------------------------- 9. ledger, lifecycle ---- */
static const char *fam_names[FR_COUNT] = { "PREPARE_VISIT", "VALIDATE_PREPARED_BOUNDARY", "FORMULA_VISIT", "FORMULA_INTERN_STEP", "COFACTOR_VISIT", "COFACTOR_REBUILD", "SUPPORT_CHUNK", "MUST_CHUNK", "COST_ADD_CHUNK", "COST_COMPARE_CHUNK", "CERTIFICATE_VISIT", "REALIZATION_VISIT", "ALLOCATE_CHUNK", "RELEASE_CHUNK", "TABLE_PROBE", "DEMAND_VISIT", "SPECIALIZE_VISIT", "FAMILY_CHUNK", "GEODESIC_VISIT", "PRODUCER_LOOKUP", "ALIAS_DELIVERY", "SHAPE_NODE", "DEPENDENCY_CHECK", "RECEIPT", "PROOF_USE_AUDIT", "SCHEDULE_STEP", "CYCLE_CHECK" };
const char *frame_family_name(FrameFamily f) { return fam_names[f]; }
WorkLedger work_ledger(void) { LOCK; WorkLedger l = W.L; UNLOCK; return l; }
void work_ledger_reset(void) { LOCK; memset(&W.L, 0, sizeof W.L); UNLOCK; }
void work_set_phase(Phase p) { LOCK; W.phase = p; UNLOCK; }
Phase work_phase(void) { return W.phase; }
uint64_t work_total_frames(void) { LOCK; uint64_t t = 0; for (int i = 0; i < FR_COUNT; i++) t += W.L.frames[i]; UNLOCK; return t; }
void work_record_execution(EvalEvents b, EvalNetEvents nb, EvalEvents a, EvalNetEvents na) {
    LOCK;
    W.L.exec_eval.request += a.request - b.request; W.L.exec_eval.eval_step += a.eval_step - b.eval_step; W.L.exec_eval.publish += a.publish - b.publish; W.L.exec_eval.deliver += a.deliver - b.deliver;
    W.L.exec_eval.ready_hit += a.ready_hit - b.ready_hit; W.L.exec_eval.running_hit += a.running_hit - b.running_hit; W.L.exec_eval.launch += a.launch - b.launch;
    W.L.exec_net.apply += na.apply - nb.apply; W.L.exec_net.continue_ref += na.continue_ref - nb.continue_ref; W.L.exec_net.op += na.op - nb.op; W.L.exec_net.eval_deliver += na.eval_deliver - nb.eval_deliver; W.L.exec_net.retries += na.retries - nb.retries;
    W.L.by_phase[PH_EXECUTE] += (a.eval_step - b.eval_step) + (na.op - nb.op) + (na.apply - nb.apply) + (na.continue_ref - nb.continue_ref);
    UNLOCK;
}

void work_init(void) {
    memset(&W, 0, sizeof W);
    pthread_mutex_init(&W.mu, NULL);
    ktab_init(&W.tab); chunked_init(&W.side, sizeof(Side)); chunked_init(&W.ops, sizeof(Handle));
    uint64_t z[4] = { K_FORMULA, FM_ZERO, 0, 0 }, one[4] = { K_FORMULA, FM_ONE, 0, 0 }, e[1] = { K_SET };
    W.ZERO = intern_sync(z, 4, NULL); W.ONE = intern_sync(one, 4, NULL); W.EMPTY = intern_sync(e, 1, NULL);
    uint64_t f0[1] = { K_FAMILY }, f1[2] = { K_FAMILY, W.EMPTY };
    W.FAM0 = intern_sync(f0, 1, NULL); W.FAM1 = intern_sync(f1, 2, NULL);
    memset(&W.L, 0, sizeof W.L);
    W.live = true;
}
void work_free(void) {
    if (!W.live) return;
    for (size_t i = 1; i <= W.tab.n; i++) {
        Side *s = side(i); if (!s->ptr) continue;
        switch (s->kind) {
        case K_JOB: { Op *o = s->ptr; for (size_t k = 0; k < o->stack.len; k++) { words_free(&o->stack.data[k].buf); words_free(&o->stack.data[k].buf2); words_free(&o->stack.data[k].buf3); } vec_free(&o->stack); vec_free(&o->waiters); vec_free(&o->path); break; }
        case K_DGRAPH: { DGraph *d = s->ptr; for (size_t k = 0; k < d->nodes.len; k++) { vec_free(&d->nodes.data[k].occ); vec_free(&d->nodes.data[k].applies); } vec_free(&d->nodes); vec_free(&d->roots); vec_free(&d->applies); wordmap_free(&d->index); break; }
        case K_DEMAND: { Demand *d = s->ptr; vec_free(&d->producers); vec_free(&d->occ); break; }
        case K_REAL: { Real *r = s->ptr; vec_free(&r->plans); vec_free(&r->conns); break; }
        case K_GEO: { Geo *g = s->ptr; vec_free(&g->edges); break; }
        default: break;
        }
    }
    for (size_t i = 0; i < W.owned.len; i++) free(W.owned.data[i]);
    vec_free(&W.owned);
    ktab_free(&W.tab); chunked_free(&W.side); chunked_free(&W.ops);
    pthread_mutex_destroy(&W.mu);
    W.live = false;
}
