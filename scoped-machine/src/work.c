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
#include "arena.h"
#include "kcont.h"
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
    uint64_t *sold; size_t sold_n, smoved, sold_cap;   /* §94: a store relocation in progress — the previous block, its extent, the copy cursor, its block size */
    uint64_t *fresh; size_t fresh_n, cleared;          /* §94: the next slot array being cleared CHUNK_WORDS per unit before the relocation into it begins */
    Chunked off;            /* record offsets: non-moving chunks (no relocation on growth) */
    uint64_t *slots; size_t nslots, n;
    uint64_t *old; size_t old_n, cursor;   /* an incremental relocation in progress (framed growth) */
    uint64_t moving; size_t probe;          /* §94.2(4): the old slot being placed and its probe cursor */
    uint64_t gen;                           /* R1: slot-array generation; a saved probe cursor is valid only for its generation */
} KTab;

static struct {
    KTab tab;
    Chunked side;
    WorkLedger L; Phase phase;          /* L: the execute-phase event projections only (exec_eval / exec_net) */
    struct { XCount frames[FR_COUNT], by_phase[PH_COUNT]; XCount probes, word_compares, limb_ops, alloc_words, release_words, memo_lookup, memo_hit, memo_deliver, kernel_calls; } LX;   /* V23 R5: the exact ledger */
    XSnap late_base[PH_COUNT][3];
    Paged dead;                         /* retired job stacks (Paged descriptors) awaiting frame-by-frame release */   /* V21 R3: late totals at the last ledger reset */
    Chunked ops; size_t nops;    /* handles */
    FormulaId ZERO, ONE; SetId EMPTY; FamilyId FAM0, FAM1;
    Paged owned;            /* kind-specific structs to free (pointers; paged) */
    pthread_mutex_t mu;
    uint64_t mark_seq;
    size_t grant, extra;        /* §94: the transitions the current unit may grant a kernel continuation; the transitions it took beyond one */
    KCont *kc_active; uint64_t kc_owner;   /* inspection only (white-box probes): the continuation most recently granted and its job — continuations are per job and independent */
    struct Spare { uint64_t *block; size_t words, cleared, need; } spare[3];   /* §94: the next chunk of the side / handle / offset tables, taken from the arena and cleared CHUNK_WORDS per unit ahead of need */
    Paged pool[16]; size_t pool_sizes[16];   /* fixed-size records (Op, Demand, Real, …) from arena pages: one slot, cleared, per record */
    uint64_t sync_clear_words;             /* words a chunk had to clear synchronously because its spare was not ready (counted) */
    bool live;
} W;

static uint64_t hash_step(uint64_t h, uint64_t w) { h ^= w + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); return h * 0xBF58476D1CE4E5B9ULL; }

#define STORE_INITIAL_WORDS ((size_t)1 << 20)   /* the store's first block: one arena allocation (address space; pages are committed on first touch) */
static void ktab_init(KTab *t) {
    words_init(&t->store); t->store.w = arena_alloc(STORE_INITIAL_WORDS, &t->store.cap); t->store.n = 0;
    t->sold = NULL; t->sold_n = t->smoved = t->sold_cap = 0; chunked_init(&t->off, sizeof(size_t));
    t->nslots = 1024; t->slots = arena_alloc(t->nslots, NULL); memset(t->slots, 0, t->nslots * sizeof(uint64_t)); t->n = 0;   /* the first slot array: 2 chunks cleared at initialization */
    t->old = NULL; t->fresh = NULL;
}
static void ktab_free(KTab *t) {
    arena_release(t->store.w, t->store.cap); words_init(&t->store);
    arena_release(t->sold, t->sold_cap); t->sold = NULL; chunked_free(&t->off);
    arena_release(t->slots, t->nslots); arena_release(t->old, t->old_n); arena_release(t->fresh, t->fresh_n);
}
/* §94: the record store never copies inside a unit. Growth allocates the new
 * block (one allocation step) and relocates the old one CHUNK_WORDS per unit
 * (`store_grow_chunk`, driven by the framed INTERN's reservation phase, and
 * completed by the synchronous paths before they touch the store). During a
 * relocation every word below the old extent is read from the old block,
 * which stays complete: a write below that extent lands in the old block and
 * is mirrored into the new one once the copy cursor has passed it. */
static const uint64_t *store_at(size_t x) { const KTab *t = &W.tab; return (t->sold && x < t->sold_n) ? t->sold + x : t->store.w + x; }
static void store_write(size_t x, uint64_t v) { KTab *t = &W.tab; if (t->sold && x < t->sold_n) { t->sold[x] = v; if (x < t->smoved) t->store.w[x] = v; } else t->store.w[x] = v; }
static size_t rec_off(uint64_t id) { return *(size_t *)chunked_get(&W.tab.off, id - 1); }
static const uint64_t *rec_words(uint64_t id, size_t *n) { size_t o = rec_off(id); const uint64_t *p = store_at(o); *n = (size_t)p[1]; return p + 2; }
static uint64_t rec_hash(uint64_t id) { return *store_at(rec_off(id)); }
static void rec_publish_off(size_t off) { KTab *t = &W.tab; *(size_t *)chunked_at(&t->off, t->n) = off; t->n++; }
static Side *side(uint64_t id) { return (Side *)chunked_at(&W.side, id - 1); }
static uint8_t rec_kind(uint64_t id) { size_t n; return (uint8_t)rec_words(id, &n)[0]; }
static uint64_t rec_w(uint64_t id, size_t i) { size_t n; const uint64_t *w = rec_words(id, &n); require(i < n, "record field"); return w[i]; }

/* synchronous interning, charged per hashed word, probe and compared word
 * (used by constructors that are not themselves framed operations; the
 * framed INTERN below performs the same steps one per frame) */
static void charge(FrameFamily f) { xc_add(&W.LX.frames[f], 1); xc_add(&W.LX.by_phase[W.phase], 1); }
/* §94.2(6): the reuse administration a kernel call performs (shape nodes
 * built, dependency checks, receipt instances) is charged into its ledger
 * families from the kernel's own counters around the call; these are
 * accounted, not resumable (see the bounded-helper table) */
/* V21 R3: each such event is charged once, to the scope that owns the work
 * executing it (reuse.h): a kernel call's continuation and the evaluator
 * tasks of the producers it launched. A closed scope's counts reach the
 * ledger through the late totals; work_ledger folds them in. No global
 * before/after snapshot spans another job's work. */
static void ledger_fold_late(WorkLedger *l) {
    static const ReuseCounter rc_of[3] = { REUSE_SHAPE_NODE, REUSE_DEPENDENCY_CHECK, REUSE_RECEIPT_INSTANCE };
    static const FrameFamily fr_of[3] = { FR_SHAPE_NODE, FR_DEPENDENCY_CHECK, FR_RECEIPT };
    for (int ph = 0; ph < PH_COUNT; ph++) for (int k = 0; k < 3; k++) {
        uint64_t v; require(xs_delta_u64(reuse_scope_late_snap(ph, rc_of[k]), W.late_base[ph][k], &v), "work ledger: a late contribution outside a machine word (read work_ledger_exact)");
        require(l->frames[fr_of[k]] <= UINT64_MAX - v && l->by_phase[ph] <= UINT64_MAX - v, "work ledger: a reading outside a machine word (read work_ledger_exact)");
        l->frames[fr_of[k]] += v; l->by_phase[ph] += v;
    }
}
/* growth: a new slot array is allocated and the old one relocated in chunks
 * of CHUNK_WORDS slots; a framed INTERN performs one chunk per frame, every
 * other probe path first completes a pending relocation (counted) */
/* §94: growth of the slot array is itself in units — one allocation unit
 * takes the next array from the arena (uncleared), then `ktab_clear_chunk`
 * zeroes CHUNK_WORDS slots per unit, and only a fully cleared array begins
 * the relocation (`ktab_begin_grow`); meanwhile the current table serves */
static bool ktab_prepare_grow(void) {   /* true when the fresh array is ready */
    KTab *t = &W.tab;
    if (!t->fresh) { size_t ns = t->nslots * 2; t->fresh = arena_alloc(ns, NULL); t->fresh_n = ns; t->cleared = 0; xc_add(&W.LX.alloc_words, ns); charge(FR_ALLOCATE_CHUNK); return false; }
    size_t end = t->cleared + CHUNK_WORDS; if (end > t->fresh_n) end = t->fresh_n;
    for (size_t x = t->cleared; x < end; x++) t->fresh[x] = 0;
    t->cleared = end; charge(FR_ALLOCATE_CHUNK);
    return t->cleared >= t->fresh_n;
}
static void ktab_prepare_grow_sync(void);
static void ktab_begin_grow(void) {
    KTab *t = &W.tab;
    if (!(t->fresh && t->cleared >= t->fresh_n)) ktab_prepare_grow_sync();   /* the framed path prepares in units first; a synchronous caller prepares here */
    t->old = t->slots; t->old_n = t->nslots; t->cursor = 0; t->gen++;
    t->slots = t->fresh; t->nslots = t->fresh_n; t->fresh = NULL; t->fresh_n = t->cleared = 0;
}
static void ktab_prepare_grow_sync(void) { while (!ktab_prepare_grow()) ; }
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
        xc_add(&W.LX.probes, 1); budget--;
        if (t->slots[t->probe]) { t->probe = (t->probe + 1) & (t->nslots - 1); continue; }
        t->slots[t->probe] = t->moving; t->moving = 0;
    }
    charge(FR_TABLE_PROBE);
    if (t->cursor >= t->old_n && !t->moving) { arena_release(t->old, t->old_n); t->old = NULL; xc_add(&W.LX.release_words, t->old_n); charge(FR_RELEASE_CHUNK); return true; }
    return false;
}
static void ktab_settle(void) { while (!ktab_grow_chunk()) ; }
static void ktab_grow(void) { ktab_settle(); ktab_prepare_grow_sync(); ktab_begin_grow(); ktab_settle(); }
/* store growth: begin = one allocation step; one relocation unit = at most
 * CHUNK_WORDS words copied; true when no relocation is pending */
static void store_begin_grow(size_t extra) {
    KTab *t = &W.tab;
    size_t nc = t->store.cap ? t->store.cap * 2 : 16;
    while (nc < t->store.n + extra) { require(nc <= SIZE_MAX / 2, "record store exhausted"); nc *= 2; }
    size_t got; uint64_t *nw = arena_alloc(nc, &got);   /* one bounded arena allocation (≤ ARENA_ORDERS split steps); no copy, no clearing */
    t->sold = t->store.w; t->sold_n = t->store.n; t->smoved = 0; t->sold_cap = t->store.cap;
    t->store.w = nw; t->store.cap = got; xc_add(&W.LX.alloc_words, got); charge(FR_ALLOCATE_CHUNK);
}
static bool store_grow_chunk(void) {
    KTab *t = &W.tab;
    if (!t->sold) return true;
    size_t end = t->smoved + CHUNK_WORDS; if (end > t->sold_n) end = t->sold_n;
    for (size_t x = t->smoved; x < end; x++) t->store.w[x] = t->sold[x];
    t->smoved = end; charge(FR_ALLOCATE_CHUNK);
    if (t->smoved >= t->sold_n) { arena_release(t->sold, t->sold_cap); t->sold = NULL; xc_add(&W.LX.release_words, t->sold_n); charge(FR_RELEASE_CHUNK); return true; }
    return false;
}
static void store_settle(void) { while (!store_grow_chunk()) ; }
static uint64_t intern_sync(const uint64_t *w, size_t n, bool *created) {
    KTab *t = &W.tab;
    ktab_settle(); store_settle();
    if (created) *created = false;
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ n;
    for (size_t i = 0; i < n; i++) { h = hash_step(h, w[i]); xc_add(&W.LX.limb_ops, 1); charge(FR_FORMULA_INTERN_STEP); }
    if ((t->n + 1) * 2 > t->nslots) ktab_grow();
    size_t j = h & (t->nslots - 1);
    for (;;) {
        xc_add(&W.LX.probes, 1); charge(FR_TABLE_PROBE);
        uint64_t id = t->slots[j];
        if (!id) break;
        if (rec_hash(id) == h) {
            size_t m; const uint64_t *v = rec_words(id, &m);
            bool eq = m == n; for (size_t i = 0; eq && i < n; i++) { xc_add(&W.LX.word_compares, 1); charge(FR_FORMULA_INTERN_STEP); eq = v[i] == w[i]; }
            if (eq) return id;
        }
        j = (j + 1) & (t->nslots - 1);
    }
    if (t->store.n + n + 2 > t->store.cap) { store_begin_grow(n + 2); store_settle(); }   /* synchronous path: the growth and its relocation run to completion here */
    size_t off = t->store.n;
    t->store.w[t->store.n++] = h; t->store.w[t->store.n++] = n;
    for (size_t i = 0; i < n; i++) { t->store.w[t->store.n++] = w[i]; xc_add(&W.LX.alloc_words, 1); charge(FR_ALLOCATE_CHUNK); }
    rec_publish_off(off);
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
        xc_add(&W.LX.probes, 1); charge(FR_TABLE_PROBE);
        uint64_t id = slots[j];
        if (!id) return 0;
        if (rec_hash(id) == h) {
            size_t m; const uint64_t *v = rec_words(id, &m);
            bool eq = m == n; for (size_t i = 0; eq && i < n; i++) { xc_add(&W.LX.word_compares, 1); charge(FR_FORMULA_INTERN_STEP); eq = v[i] == w[i]; }
            if (eq) return id;
        }
        j = (j + 1) & (nslots - 1);
    }
}
static uint64_t find_sync(const uint64_t *w, size_t n) {
    KTab *t = &W.tab;
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ n;
    for (size_t i = 0; i < n; i++) { h = hash_step(h, w[i]); xc_add(&W.LX.limb_ops, 1); charge(FR_FORMULA_INTERN_STEP); }
    uint64_t id = find_in(t->slots, t->nslots, h, w, n);
    if (!id && t->old) id = find_in(t->old, t->old_n, h, w, n);
    return id;
}
static void *own(void *p) { *(void **)paged_push(&W.owned) = p; return p; }
/* §94: the engine's fixed-size records come from arena pages (a slot per
 * record, cleared: a constant-size initialization); its chunked tables take
 * their chunks from spares the engine clears CHUNK_WORDS per unit ahead of
 * need (`arena_tend`, one step per unit); a chunk needed before its spare is
 * ready clears the remainder synchronously, counted in `sync_clear_words`.
 * No host allocation remains on a unit's path. */
static void *pool_take(size_t bytes) {
    size_t k = 0; while (k < 16 && W.pool_sizes[k] && W.pool_sizes[k] != bytes) k++;
    require(k < 16, "record pools exhausted");
    if (!W.pool_sizes[k]) { W.pool_sizes[k] = bytes; paged_init(&W.pool[k], bytes); }
    void *p = paged_push(&W.pool[k]); memset(p, 0, bytes); return p;
}
static void spare_init(struct Spare *sp, size_t bytes) { sp->need = (bytes + 7) / 8; sp->block = NULL; sp->words = sp->cleared = 0; }
static bool spare_tend(struct Spare *sp) {   /* one bounded step; true when the spare is ready */
    if (!sp->block) { sp->block = arena_alloc(sp->need, &sp->words); sp->cleared = 0; xc_add(&W.LX.alloc_words, sp->words); charge(FR_ALLOCATE_CHUNK); return false; }
    if (sp->cleared >= sp->need) return true;
    size_t end = sp->cleared + CHUNK_WORDS; if (end > sp->need) end = sp->need;
    for (size_t x = sp->cleared; x < end; x++) sp->block[x] = 0;
    sp->cleared = end; charge(FR_ALLOCATE_CHUNK);
    return sp->cleared >= sp->need;
}
static void *chunk_from_spare(size_t bytes, void *ctx) {
    struct Spare *sp = ctx; require((bytes + 7) / 8 == sp->need, "chunk size");
    while (!spare_tend(sp)) if (sp->block && sp->cleared < sp->need) W.sync_clear_words += CHUNK_WORDS;   /* not ready: the remainder is cleared here, counted */
    void *b = sp->block; sp->block = NULL; sp->words = sp->cleared = 0;
    return b;
}
static void dead_stack_step(void);
static void arena_tend(void) {   /* one maintenance step per unit: a retired page, and one clearing step of the first spare that needs it */
    if (arena_reap()) charge(FR_RELEASE_CHUNK);
    if (arena_tend_zero()) charge(FR_ALLOCATE_CHUNK);   /* one clearing step of a retired zero block (§94 R4) */
    for (int i = 0; i < 3; i++) if (!W.spare[i].block || W.spare[i].cleared < W.spare[i].need) { spare_tend(&W.spare[i]); break; }
    dead_stack_step();   /* one frame of a restarted job's old stack */
}

/* ---------------------------------------------------------------- 2. frames ---- */
typedef struct DGraph DGraph; typedef struct Geo Geo;
static uint64_t dgraph_rev(const DGraph *g); static uint64_t geo_rev(const Geo *g);

enum {   /* operation families (frame kinds) */
    OF_INTERN = 1, OF_LOOKUP, OF_MKF, OF_RESTRICT, OF_SUPPORT, OF_MUST, OF_SUBST, OF_SUM, OF_SETOP, OF_DEMAND, OF_EXTRACT,
    OF_SPEC_SET, OF_SPEC_FORMULA, OF_PREPARE, OF_EXPRF, OF_REALIZE, OF_REALVISIT, OF_CHECKCERT, OF_PROOF, OF_REDUCE, OF_ANTICHAIN,
    OF_FAMOP, OF_NORMALIZE, OF_SUBSET, OF_GEO, OF_MAPF, OF_MAPP, OF_MAPSET, OF_ATOMSPEC, OF_LIST, OF_SORT,
    OF_JOIN,  /* §94.2(4): the bounded request of a shared operation — key interning, then join/create/deliver */
    OF_BOUNDARY, /* shared expression-boundary computation, one node phase per unit */
    OF_SYMS, OF_EDGES, OF_AUDIT,  /* §94: shared audit judgments with private traversal helpers */
    OF_KERNEL                     /* §94: a kernel call as a continuation stepped one fine transition per unit (kcont.h); a = kind */
};
/* the kernel calls units make (kcont.h): pure ones are shared jobs keyed by
 * their operands (and the checker session / environment version where the
 * call reads them); the evaluator-state lookup is private */
enum { KK_REINDEX = 1, KK_COMPOSE, KK_FC_REINDEX, KK_REF_VALIDATE, KK_FC_PROJECT, KK_ENTAILS, KK_ENTRY_LOOKUP, KK_SHAPE_OF,
       KK_INFER, KK_ADMISSION, KK_CONTEXT, KK_IS_TYPE, KK_CHECK, KK_TRANSFORM_EVIDENCE, KK_NAT };
enum { CA_ADD = 1, CA_MIN, CA_CMP };   /* KK_NAT operations on costs (BOUNDS-COMPLETION §3) */
enum { SO_UNION = 1, SO_INTER, SO_DIFF };

typedef struct {
    uint16_t fam, ph;
    uint64_t a, b, c, d, e;      /* operands */
    uint64_t i, j;               /* component indices */
    uint64_t acc, acc2, acc3, acc4;
    Paged buf, buf2, buf3;       /* owned variable data: paged word buffers (§§89/94: O(1) push/read/write, fixed pages from the arena, no copy on growth) */
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
    Paged stack;                 /* frames: paged (§94: O(1) push/pop, no copy on growth) */
    Phase phase; int family;
    uint64_t waiting_on;         /* job id this job is suspended on, 0 when enabled */
    bool kwait;                  /* V21 R2: the wait is a kernel continuation's predicate wait (rechecked after each unit of the dependency), not a JOIN */
    uint64_t unresolved;         /* §94 R2: the checker attempt in which this job failed UNRESOLVED (0: a settled outcome); a request in a later attempt restarts it */
    Paged waiters;               /* jobs suspended on this job (one registration per join; delivered one per unit); paged */
    uint64_t frames;
    /* §94.2(2–3): the cone path of this job when it is driven as a root:
     * the chain root → … → tip, extended or popped one hop per unit */
    Paged path;
} Op;                            /* historical name: the job record */
typedef struct { uint64_t job; uint64_t frames; bool released; } Handle;

#define RULES_VERSION 1          /* the fixed proof-rule / direct-reduction rule set of this build */
static void frame_free(Frame *f);
static Op *JOB(uint64_t id) { Op *o = (Op *)side(id)->ptr; require(o && side(id)->kind == K_JOB, "not a job"); return o; }
static Handle *HND(OpId h) { require(h && h <= W.nops, "unknown operation handle"); return (Handle *)chunked_get(&W.ops, h - 1); }
static bool shared_family(uint16_t fam) {
    switch (fam) { case OF_INTERN: case OF_LOOKUP: case OF_LIST: case OF_NORMALIZE: case OF_REALVISIT: case OF_SORT: case OF_SYMS: case OF_EDGES: return false; default: return true; }   /* AUDIT is a shared judgment producer; SYMS/EDGES are private helpers with completed-result memos. */
}
/* the persistent key of a shared frame: family, operands, and the external
 * versions the operation reads (§75.1) */
static size_t job_key(const Frame *f, uint64_t *w) {
    size_t n = 0; w[n++] = K_JOB; w[n++] = f->fam; w[n++] = f->a; w[n++] = f->b; w[n++] = f->c; w[n++] = f->d;
    switch (f->fam) {
    case OF_PROOF: case OF_REDUCE: w[n++] = RULES_VERSION; break;
    case OF_SPEC_SET: case OF_SPEC_FORMULA: case OF_ATOMSPEC: w[n++] = global_env_version(); break;
    case OF_PREPARE: case OF_CHECKCERT: case OF_AUDIT: w[n++] = check_session_id(); w[n++] = global_env_version(); break;
    case OF_GEO: w[n++] = geo_rev((Geo *)side(f->a)->ptr); break;
    case OF_DEMAND: w[n++] = dgraph_rev((DGraph *)side(f->a)->ptr); break;
    case OF_KERNEL: w[n++] = f->e; if (f->a >= KK_INFER) { w[n++] = check_session_id(); w[n++] = global_env_version(); } break;
    default: break;
    }
    return n;
}
static Phase phase_of_family(uint16_t fam) {
    switch (fam) {
    case OF_BOUNDARY: case OF_PREPARE: case OF_EXPRF: case OF_DEMAND: case OF_EXTRACT: case OF_SPEC_SET: case OF_SPEC_FORMULA: case OF_ATOMSPEC: case OF_MAPF: case OF_MAPP: case OF_MAPSET: return PH_PREPARE;
    case OF_CHECKCERT: case OF_PROOF: case OF_GEO: case OF_AUDIT: case OF_KERNEL: return PH_CHECK;
    case OF_REALIZE: return PH_COMMIT;
    default: return PH_REWRITE;
    }
}
static Op *op_new_record(uint64_t id, uint16_t fam) {   /* a fixed-size host allocation (constant) */
    Op *o = pool_take(sizeof *o);
    o->id = id; o->st = OP_RUNNING; o->phase = phase_of_family(fam); o->family = fam;
    paged_init(&o->stack, sizeof(Frame)); paged_init(&o->waiters, sizeof(uint64_t)); paged_init(&o->path, sizeof(uint64_t));
    return o;
}
/* §94 R2: a job that failed UNRESOLVED in an earlier checker attempt is not a
 * settled verdict — a request in a later attempt restarts it from the
 * requested frame (its completed dependencies are READY jobs and are joined
 * again, not recomputed); a settled outcome, valid or invalid, is reused */
static void frame_free(Frame *f);
static bool job_restart_if_stale(Op *o, const Frame *f) {
    if (o->st != OP_INVALID || !o->unresolved || o->unresolved == check_attempt()) return false;
    /* the old frames are handed to the dead-stack queue in one step and
     * released one frame per unit (dead_stack_step) — no input-sized loop
     * here (V21 review: reachable from a framed JOIN through job_at) */
    *(Paged *)paged_push(&W.dead) = o->stack; paged_init(&o->stack, sizeof(Frame));
    paged_retire(&o->path); paged_init(&o->path, sizeof(uint64_t));
    o->st = OP_RUNNING; o->diag = NULL; o->unresolved = 0; o->waiting_on = 0; o->ret = 0; o->result = 0;
    *(Frame *)paged_push(&o->stack) = *f;
    return true;
}
/* find or create the job of a shared frame; *created tells whether its stack was just started */
static Op *job_for(Frame f, bool *created) {
    uint64_t w[10]; size_t n = job_key(&f, w);
    if (!shared_family(f.fam)) { w[1] = f.fam; w[2] = ++W.mark_seq; n = 3; }   /* a private root (buffer-carrying) is never shared */
    bool fresh; uint64_t id = intern_sync(w, n, &fresh);
    xc_add(&W.LX.probes, 1); xc_add(&W.LX.memo_lookup, 1); charge(FR_PRODUCER_LOOKUP);
    Side *sd = side(id);
    if (sd->ptr && ((Op *)sd->ptr)->st == OP_COMPLETE) xc_add(&W.LX.memo_hit, 1);
    if (!sd->ptr) {
        Op *o = op_new_record(id, f.fam);
        *(Frame *)paged_push(&o->stack) = f;
        sd->ptr = o; sd->kind = K_JOB;
        *created = true;
        return o;
    }
    if (job_restart_if_stale((Op *)sd->ptr, &f)) { *created = true; return (Op *)sd->ptr; }
    frame_free(&f);
    *created = false;
    return (Op *)sd->ptr;
}
static Frame fr(uint16_t fam, uint64_t a, uint64_t b, uint64_t c, uint64_t d) { Frame f; memset(&f, 0, sizeof f); f.fam = fam; f.a = a; f.b = b; f.c = c; f.d = d; paged_init(&f.buf, sizeof(uint64_t)); paged_init(&f.buf2, sizeof(uint64_t)); paged_init(&f.buf3, sizeof(uint64_t)); return f; }
static void frame_free(Frame *f) {   /* O(1): the pages are retired and released one per unit (arena_reap in op_step) */
    size_t n = f->buf.n + f->buf2.n;
    xc_add(&W.LX.release_words, n); if (n) charge(FR_RELEASE_CHUNK);
    paged_retire(&f->buf); paged_retire(&f->buf2); paged_retire(&f->buf3);
}
/* one frame of the first dead stack per call; the empty stack's pages are then retired */
static void dead_stack_step(void) {
    if (!W.dead.n) return;
    Paged *st = (Paged *)paged_at(&W.dead, W.dead.n - 1);
    if (st->n) { frame_free((Frame *)paged_at(st, st->n - 1)); paged_pop(st); return; }
    paged_retire(st); paged_pop(&W.dead);
}
static void pw_append(Paged *p, const uint64_t *w, size_t n) { for (size_t i = 0; i < n; i++) pw_push(p, w[i]); }   /* bounded callers pass fixed-size keys; synchronous entries pass their inputs */
static Frame *top(Op *o) { return (Frame *)paged_at(&o->stack, o->stack.n - 1); }
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
    if (!shared_family(f.fam) || (f.fam == OF_KERNEL && f.a == KK_ENTRY_LOOKUP)) { *(Frame *)paged_push(&o->stack) = f; return; }   /* the evaluator-state lookup is not a pure function of its operands: private */
    require(f.buf.n == 0 && f.buf2.n == 0 && f.buf3.n == 0, "a shared frame carries no buffer");
    Frame j = fr(OF_JOIN, f.a, f.b, f.c, f.d); j.acc = f.fam; j.e = f.e;
    uint64_t w[10]; size_t n = job_key(&f, w); pw_append(&j.buf, w, n);
    frame_free(&f);
    *(Frame *)paged_push(&o->stack) = j;
}
/* the job record of a key (created when absent, with the requested frame) */
static Op *job_at(uint64_t id, const Frame *f, bool *created) {
    Side *sd = side(id);
    *created = false;
    if (sd->ptr && ((Op *)sd->ptr)->st == OP_COMPLETE) xc_add(&W.LX.memo_hit, 1);
    if (!sd->ptr) {
        Op *o = op_new_record(id, f->fam);
        *(Frame *)paged_push(&o->stack) = *f;
        sd->ptr = o; sd->kind = K_JOB;
        *created = true;
    } else if (job_restart_if_stale((Op *)sd->ptr, f)) *created = true;
    return (Op *)sd->ptr;
}
/* one delivery: the finished job j answers waiter w (one unit, charged) */
static void deliver_to(Op *w, Op *j) {
    w->waiting_on = 0;
    if (w->stack.n && top(w)->fam == OF_KERNEL && top(w)->ph == 1) return;   /* a continuation that waited for j's continuation: it re-examines its own condition */
    if (j->st == OP_COMPLETE) { w->ret = j->result; xc_add(&W.LX.memo_deliver, 1); charge(FR_ALIAS_DELIVERY); reuse_bump(REUSE_READY_HIT); }
    else if (j->st == OP_INVALID) { if (j->unresolved) w->unresolved = j->unresolved; fail(w, j->diag); }   /* an attempt-local failure stays attempt-local in the dependents */
    else limit(w, j->diag);
}
static void step_join(Op *o, Frame *f) {
    switch (f->ph) {
    case 0: { uint64_t w[10]; size_t n = f->buf.n; require(n <= 10, "job key"); for (size_t i = 0; i < n; i++) w[i] = pw_get(&f->buf, i); f->ph = 1; push_intern(o, w, n); return; }
    case 1: {
        Frame g = fr((uint16_t)f->acc, f->a, f->b, f->c, f->d); g.e = f->e;
        bool created; Op *j = job_at(o->ret, &g, &created);
        if (!created) frame_free(&g);
        xc_add(&W.LX.memo_lookup, 1);
        if (j == o) { fail(o, "cyclic request: an operation requested itself"); return; }
        if (j->st != OP_RUNNING) { frame_free(f); paged_pop(&o->stack); deliver_to(o, j); return; }
        if (created) { frame_free(f); paged_pop(&o->stack); o->waiting_on = j->id; o->kwait = false; pw_push(&j->waiters, o->id); return; }
        /* join a running job: the cycle check walks j's chain one hop per
         * unit before the wait is committed (§94.2(3)) */
        reuse_bump(REUSE_RUNNING_JOIN);
        f->ph = 2; f->acc2 = j->id; f->acc3 = j->id; return;
    }
    case 2: {   /* one hop of the cycle check */
        charge(FR_CYCLE_CHECK);
        Op *j = JOB(f->acc2);
        if (j->st != OP_RUNNING) { frame_free(f); paged_pop(&o->stack); deliver_to(o, j); return; }
        Op *c = JOB(f->acc3);
        uint64_t next = c->st == OP_RUNNING ? c->waiting_on : 0;
        if (next == o->id) { fail(o, "cyclic request among running operations"); return; }
        if (next) { f->acc3 = next; return; }
        frame_free(f); paged_pop(&o->stack); o->waiting_on = j->id; o->kwait = false; pw_push(&j->waiters, o->id); return;
    }
    }
}
static void stack_drop(Op *o) { for (size_t i = 0; i < o->stack.n; i++) frame_free((Frame *)paged_at(&o->stack, i)); paged_retire(&o->stack); }   /* reached with an empty stack from fin; the synchronous release otherwise */
static void fin(Op *o, uint64_t v) { Frame *t = top(o); frame_free(t); paged_pop(&o->stack); o->ret = v; if (!o->stack.n) { o->st = OP_COMPLETE; o->result = v; stack_drop(o); } }
static void fail(Op *o, const char *why) { if (o->st != OP_RUNNING) return; o->st = OP_INVALID; o->diag = why; }   /* retained frames are released one per unit by the scheduler (§94.2(5)) */
static void limit(Op *o, const char *why) { if (o->st != OP_RUNNING) return; o->st = OP_RESOURCE_LIMIT; o->diag = why; }   /* state retained, not resumable */

/* exact natural arithmetic (nat.h): one limb operation per limb; the sum is
 * always representable (INFINITY absorbs) */
static bool add_checked(Cost a, Cost b, Cost *out) { xc_add(&W.LX.limb_ops, 1); *out = cost_sum(a, b); return true; }
Cost cost_add(Cost a, Cost b, bool *overflow) { if (overflow) *overflow = false; return cost_sum(a, b); }

/* ---- the frame bodies ---- */
static bool cost_op(Op *o, Frame *f, int kind, Cost a, Cost b, uint16_t resume, Cost *out);
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
static void step_boundary(Op *o, Frame *f);
static void step_syms(Op *o, Frame *f);
static void step_edges(Op *o, Frame *f);
static void step_audit(Op *o, Frame *f);
static void step_kernel(Op *o, Frame *f);
static Frame kfr(uint64_t kind, uint64_t b, uint64_t c, uint64_t d, uint64_t e);
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
    case OF_BOUNDARY: return FR_VALIDATE_PREPARED_BOUNDARY;
    case OF_SYMS: case OF_EDGES: case OF_AUDIT: return FR_PROOF_USE_AUDIT;
    case OF_KERNEL: return FR_KERNEL_TRANSITION;
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
    case OF_BOUNDARY: step_boundary(o, f); break;
    case OF_SYMS: step_syms(o, f); break;
    case OF_EDGES: step_edges(o, f); break;
    case OF_AUDIT: step_audit(o, f); break;
    case OF_KERNEL: step_kernel(o, f); break;
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
static Op *tip_of(Op *root) { return root->path.n ? JOB(pw_get(&root->path, root->path.n - 1)) : root; }
static bool service(Op *root) {
    Op *t = tip_of(root);
    Phase saved = W.phase; W.phase = root->phase;   /* charged to the requesting root's phase */
    bool progressed = true;
    if (t->st != OP_RUNNING) {
        if (t->stack.n) { frame_free(top(t)); paged_pop(&t->stack); if (!t->stack.n) paged_retire(&t->stack); charge(FR_RELEASE_CHUNK); }   /* retained frames of a failed job, one per unit */
        else if (!root->path.n) progressed = false;                   /* the root itself is finished */
        else { paged_pop(&root->path); Op *w = tip_of(root); if (w->waiting_on == t->id && w->kwait) { w->waiting_on = 0; w->kwait = false; charge(FR_SCHEDULE_STEP); } else if (w->waiting_on == t->id) deliver_to(w, t); else charge(FR_SCHEDULE_STEP); }
    } else if (t->waiting_on) {
        Op *n = JOB(t->waiting_on);
        if (n->st != OP_RUNNING && t->kwait) { t->waiting_on = 0; t->kwait = false; charge(FR_SCHEDULE_STEP); }   /* a predicate wait: the dependency finished; the waiter rechecks */
        else if (n->st != OP_RUNNING) deliver_to(t, n);
        else { pw_push(&root->path, n->id); charge(FR_SCHEDULE_STEP); }
    } else {
        step(t);
        /* V21 R2: a kernel predicate wait is revalidated after one unit of its
         * dependency: the waiter is stepped again (its continuation rechecks
         * the awaited predicate and, if it still holds, waits again) — the
         * wait is on that predicate, not on the dependency's whole call */
        if (root->path.n && t->st == OP_RUNNING) {
            Op *below = root->path.n >= 2 ? JOB(pw_get(&root->path, root->path.n - 2)) : root;
            if (below->waiting_on == t->id && below->kwait) { paged_pop(&root->path); below->waiting_on = 0; below->kwait = false; }
        }
    }
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
    while (root->st == OP_RUNNING && budget) {
        W.grant = budget; W.extra = 0;
        if (!service(root)) break;
        size_t took = 1 + W.extra; if (took > budget) took = budget;   /* a kernel continuation may take several transitions in one hand-off, each a unit */
        budget -= took; hd->frames += took;
        arena_tend();   /* one retired page released and one spare-chunk clearing step per unit (§94) */
    }
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
    while (o->st == OP_RUNNING) { W.grant = KC_UNBOUNDED; W.extra = 0; if (!service(o)) break; arena_tend(); }   /* the synchronous driver grants a kernel continuation its whole run in one hand-off */
    if (o->st != OP_COMPLETE) { if (why) *why = o->st == OP_RUNNING ? "operation suspended: no enabled job (cyclic wait)" : o->diag; return 0; }
    return o->result;
}
/* the synchronous entry of a shared operation: find or start its job
 * (counting the lookup and, for a completed answer, its delivery) */
static Op *job_sync(Frame f) {
    bool created; Op *j = job_for(f, &created);
    if (!created && j->st == OP_COMPLETE) { xc_add(&W.LX.memo_deliver, 1); charge(FR_ALIAS_DELIVERY); reuse_bump(REUSE_READY_HIT); }
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
        if (f->i < f->buf.n) { f->acc = hash_step(f->acc, pw_get(&f->buf, f->i)); f->i++; xc_add(&W.LX.limb_ops, 1); return; }
        if (t->old) { f->ph = 4; return; }
        if ((t->n + 1) * 2 > t->nslots) { if (!ktab_prepare_grow()) return; ktab_begin_grow(); f->ph = 4; return; }   /* growth: one allocation unit, CHUNK_WORDS cleared per unit, then relocation units */
        f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; return;
    case 4:   /* one relocation unit */
        if (ktab_grow_chunk()) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; }
        return;
    case 1: {   /* one probe */
        if (t->old) { f->ph = 4; return; }
        if (f->e != t->gen) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; }   /* the table changed since this cursor was taken */
        xc_add(&W.LX.probes, 1);
        uint64_t id = t->slots[f->j];
        if (!id) {
            if (!f->acc4) { f->ph = 5; return; }                                 /* no candidate yet: reserve */
            /* publish the complete candidate at this slot */
            rec_publish_off((size_t)f->acc2);
            uint64_t nid = t->n; t->slots[f->j] = nid;
            Side *sd = side(nid); memset(sd, 0, sizeof *sd); sd->kind = (uint8_t)pw_get(&f->buf, 0);
            o->ret = 0; fin(o, nid); o->ret = nid; return;
        }
        if (rec_hash(id) == f->acc) { size_t m; rec_words(id, &m); if (m == f->buf.n) { f->acc3 = id; f->i = 0; f->ph = 2; return; } }
        f->j = (f->j + 1) & (t->nslots - 1); return;
    }
    case 2: {   /* compare one word */
        if (t->old || f->e != t->gen) { f->ph = 1; return; }                     /* re-probe: the table moved under the comparison */
        size_t m; const uint64_t *v = rec_words(f->acc3, &m);
        xc_add(&W.LX.word_compares, 1);
        if (f->i < m) { if (v[f->i] != pw_get(&f->buf, f->i)) { f->j = (f->j + 1) & (t->nslots - 1); f->ph = 1; return; } f->i++; return; }
        if (f->acc4) { xc_add(&W.LX.release_words, f->buf.n + 2); charge(FR_RELEASE_CHUNK); }   /* an equal key was interned meanwhile: the candidate is abandoned */
        fin(o, f->acc3); return;
    }
    case 5: {   /* reserve an exclusive extent; only copied payload is published */
        require(t->store.n <= SIZE_MAX - 2 && f->buf.n <= SIZE_MAX - t->store.n - 2, "record extent overflow");
        if (t->sold) { store_grow_chunk(); return; }                                /* a store relocation in progress: one unit of it, then re-check */
        if (t->store.n + f->buf.n + 2 > t->store.cap) { store_begin_grow(f->buf.n + 2); return; }   /* growth: one allocation unit; the copy proceeds in units */
        f->acc2 = t->store.n;
        t->store.n += f->buf.n + 2;
        store_write(f->acc2, f->acc);
        store_write(f->acc2 + 1, f->buf.n);
        xc_add(&W.LX.alloc_words, f->buf.n + 2); charge(FR_ALLOCATE_CHUNK);
        f->i = 0; f->ph = 3; return;
    }
    case 3: {   /* copy one word into the reserved extent; then re-probe with the candidate held */
        if (f->i < f->buf.n) { store_write(f->acc2 + 2 + f->i, pw_get(&f->buf, f->i)); f->i++; return; }
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
        if (f->i < f->buf.n) { f->acc = hash_step(f->acc, pw_get(&f->buf, f->i)); f->i++; xc_add(&W.LX.limb_ops, 1); return; }
        f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; return;
    case 3:   /* one relocation unit of a growth in progress, then re-probe */
        if (ktab_grow_chunk()) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; f->ph = 1; }
        return;
    case 1: {
        if (t->old) { f->ph = 3; return; }
        if (f->e != t->gen) { f->j = f->acc & (t->nslots - 1); f->e = t->gen; }
        xc_add(&W.LX.probes, 1);
        uint64_t id = t->slots[f->j];
        if (!id) { fin(o, 0); return; }
        if (rec_hash(id) == f->acc) { size_t m; rec_words(id, &m); if (m == f->buf.n) { f->acc3 = id; f->i = 0; f->ph = 2; return; } }
        f->j = (f->j + 1) & (t->nslots - 1); return;
    }
    case 2: {
        if (t->old || f->e != t->gen) { f->ph = 1; return; }
        size_t m; const uint64_t *v = rec_words(f->acc3, &m);
        xc_add(&W.LX.word_compares, 1);
        if (f->i < m) { if (v[f->i] != pw_get(&f->buf, f->i)) { f->j = (f->j + 1) & (t->nslots - 1); f->ph = 1; return; } f->i++; return; }
        fin(o, f->acc3); return;
    }
    }
}
static Frame fr_intern(const uint64_t *w, size_t n) { Frame f = fr(OF_INTERN, 0, 0, 0, 0); pw_append(&f.buf, w, n); return f; }
/* §94.2(1): a frame's exclusive buffer becomes the child's key in constant
 * work (ownership transfer, no copy); the donor is left empty */
static Frame fr_intern_own(Paged *w) { Frame f = fr(OF_INTERN, 0, 0, 0, 0); paged_take(&f.buf, w); return f; }
static Frame fr_lookup(const uint64_t *w, size_t n) { Frame f = fr(OF_LOOKUP, 0, 0, 0, 0); pw_append(&f.buf, w, n); return f; }
static void push_intern(Op *o, const uint64_t *w, size_t n) { push(o, fr_intern(w, n)); }
static void push_intern_own(Op *o, Paged *w) { push(o, fr_intern_own(w)); }
static void push_lookup(Op *o, const uint64_t *w, size_t n) { xc_add(&W.LX.memo_lookup, 1); push(o, fr_lookup(w, n)); }
static Cost kind_weight(ModelId m, AtomId a);
/* §94: fixed-key indices consulted from a unit go through the framed LOOKUP
 * (one hashed word / one probe / one compared word per unit); the delivered
 * record id is read by these */
static Cost weight_from(uint64_t ret, ModelId m, AtomId a) { if (ret && side(ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); return side(ret)->val; } return kind_weight(m, a); }
static void push_weight_lookup(Op *o, ModelId m, AtomId a) { uint64_t k[3] = { K_WEIGHT, m, a }; push_lookup(o, k, 3); }
static AtomId amap_from(uint64_t ret, AtomId a) { if (ret && side(ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); return side(ret)->val; } return a; }
static void push_amap_lookup(Op *o, AtomMapId m, AtomId a) { uint64_t e[4] = { K_MEMO, 0xA3, m, a }; push_lookup(o, e, 4); }

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
    FaceId eta = fc_project(chi, S, n); xc_add(&W.LX.kernel_calls, 2);
    LOCK; xc_add(&W.LX.kernel_calls, 2); int ph = W.phase; UNLOCK;
    ReuseScope sc; memset(&sc, 0, sizeof sc); sc.phase = ph; sc.refs = 1;   /* this synchronous call's own accounting scope */
    ReuseScope *prev = reuse_scope_enter(&sc);
    EntryId e = eval_entry_lookup(t, eta); ShapeId sh = shape_of(t);
    reuse_scope_leave(prev); reuse_scope_close(&sc);
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

static int cmp_counted(const void *a, const void *b) { xc_add(&W.LX.word_compares, 1); uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y ? 1 : 0; }
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
bool set_has(SetId s, AtomId a) { size_t n; const AtomId *x = set_atoms(s, &n); size_t lo = 0, hi = n; while (lo < hi) { size_t mid = (lo + hi) / 2; xc_add(&W.LX.word_compares, 1); charge(FR_SUPPORT_CHUNK); if (x[mid] == a) return true; if (x[mid] < a) lo = mid + 1; else hi = mid; } return false; }
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
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; }
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
        xc_add(&W.LX.memo_lookup, 1);
        if (cached) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, cached); return; }
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO) { if (must) { fail(o, "Must is defined on nonzero formulas only"); return; } fin(o, W.EMPTY); return; }
        if (t == FM_ONE) { fin(o, W.EMPTY); return; }
        if (t == FM_ATOM) { uint64_t w[2] = { K_SET, formula_atom_of(F) }; f->ph = 4; push_intern(o, w, 2); return; }
        f->ph = 1; push(o, fr(f->fam, formula_left(F), 0, 0, 0)); return;
    }
    case 1: f->acc = o->ret; f->ph = 2; push(o, fr(f->fam, formula_right(F), 0, 0, 0)); return;
    case 2: f->acc2 = o->ret; f->i = f->j = 0; f->ph = 3; pw_push(&f->buf, K_SET); return;
    case 3: {
        size_t na, nb; const AtomId *A = set_atoms(f->acc, &na), *B = set_atoms(f->acc2, &nb);
        bool inter = must && formula_tag(F) == FM_OR;
        xc_add(&W.LX.word_compares, 1);
        if (f->i < na && f->j < nb) {
            if (A[f->i] == B[f->j]) { pw_push(&f->buf, A[f->i]); f->i++; f->j++; }
            else if (A[f->i] < B[f->j]) { if (!inter) pw_push(&f->buf, A[f->i]); f->i++; }
            else { if (!inter) pw_push(&f->buf, B[f->j]); f->j++; }
            return;
        }
        if (!inter) { if (f->i < na) { pw_push(&f->buf, A[f->i++]); return; } if (f->j < nb) { pw_push(&f->buf, B[f->j++]); return; } }
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
    if (f->ph == 0) { pw_push(&f->buf, K_SET); f->ph = 1; return; }
    if (f->ph == 2) { fin(o, o->ret); return; }
    xc_add(&W.LX.word_compares, 1);
    if (f->i < na && f->j < nb) {
        AtomId x = A[f->i], y = B[f->j];
        if (x == y) { if (f->a != SO_DIFF) pw_push(&f->buf, x); f->i++; f->j++; }
        else if (x < y) { if (f->a != SO_INTER) pw_push(&f->buf, x); f->i++; }
        else { if (f->a == SO_UNION) pw_push(&f->buf, y); f->j++; }
        return;
    }
    if (f->i < na) { if (f->a != SO_INTER) pw_push(&f->buf, A[f->i]); f->i++; return; }
    if (f->j < nb) { if (f->a == SO_UNION) pw_push(&f->buf, B[f->j]); f->j++; return; }
    f->ph = 2; push_intern_own(o, &f->buf);
}
static SetId setop(int kind, SetId a, SetId b) { return run_op(OF_SETOP, W.phase, fr(OF_SETOP, kind, a, b, 0), NULL); }
SetId set_union(SetId a, SetId b) { LOCK; SetId s = setop(SO_UNION, a, b); UNLOCK; return s; }
SetId set_inter(SetId a, SetId b) { LOCK; SetId s = setop(SO_INTER, a, b); UNLOCK; return s; }
SetId set_diff(SetId a, SetId b) { LOCK; SetId s = setop(SO_DIFF, a, b); UNLOCK; return s; }
/* SUBSET: a = A, b = B: merge-walk; result 1/0 */
static void step_subset(Op *o, Frame *f) {
    size_t na, nb; const AtomId *A = set_atoms(f->a, &na), *B = set_atoms(f->b, &nb);
    xc_add(&W.LX.word_compares, 1);
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
static void step_sum(Op *o, Frame *f) {
    size_t n; const AtomId *S = set_atoms(f->a, &n);
    switch (f->ph) {
    case 0:
        if (f->i >= n) { fin(o, f->acc); return; }
        { uint64_t k[3] = { K_WEIGHT, f->b, S[f->i] }; f->ph = 1; push_lookup(o, k, 3); return; }
    case 1: {
        Cost w = (o->ret && side(o->ret)->has_val) ? side(o->ret)->val : kind_weight(f->b, S[f->i]);
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); }
        Cost r; if (!cost_op(o, f, CA_ADD, f->acc, w, 2, &r)) return; o->ret = r;
    }
    /* fall through */
    case 2: f->acc = o->ret; f->i++; f->ph = 0; return;
    }
}
Cost set_weight(SetId s, ModelId m, bool *overflow) {
    LOCK; Op *o = job_sync(fr(OF_SUM, s, m, 0, 0));
    uint64_t r = run_locked(o, NULL); bool ov = o->st == OP_RESOURCE_LIMIT;
    UNLOCK; if (overflow) *overflow = ov; return r;
}
OpId op_set_weight(SetId s, ModelId m) { LOCK; OpId h = op_new(OF_SUM, PH_REWRITE, fr(OF_SUM, s, m, 0, 0)); UNLOCK; return h; }

/* SORT: a = record kind (K_SET / K_FAMILY), buf = elements. In-place heap
 * sort — one sift per frame (at most 64 compares and swaps, the heap depth of
 * a 64-bit index space) — then one element per frame of deduplication, then
 * the record is interned. The bounded API never sorts inside one frame. */
static void sift_down(Paged *h, size_t n, size_t i) {   /* at most 64 iterations, 128 charged comparisons (64-bit index space) */
    for (;;) {
        size_t l = 2 * i + 1, r = l + 1, m = i; xc_add(&W.LX.word_compares, 2);
        uint64_t hm = pw_get(h, i), hl = l < n ? pw_get(h, l) : 0, hr = r < n ? pw_get(h, r) : 0;
        if (l < n && hl > hm) { m = l; hm = hl; }
        if (r < n && hr > hm) { m = r; hm = hr; }
        if (m == i) return;
        uint64_t t = pw_get(h, i); pw_set(h, i, hm); pw_set(h, m, t); i = m;
    }
}
static void step_sort(Op *o, Frame *f) {
    size_t n = f->buf.n;
    switch (f->ph) {
    case 0: if (n < 2) { f->ph = 2; f->i = 0; f->j = 0; return; } f->i = n / 2; f->ph = 1; return;
    case 1:   /* build: sift index i-1; then extract from the end */
        if (f->i > 0) { f->i--; sift_down(&f->buf, n, f->i); return; }
        if (f->j == 0) f->j = n;
        if (f->j > 1) { f->j--; uint64_t t = pw_get(&f->buf, 0); pw_set(&f->buf, 0, pw_get(&f->buf, f->j)); pw_set(&f->buf, f->j, t); sift_down(&f->buf, f->j, 0); return; }
        f->ph = 2; f->i = 0; f->j = 0; return;
    case 2:   /* dedupe: buf2 collects */
        if (f->j == 0) { pw_push(&f->buf2, f->a); f->j = 1; }
        if (f->i < n) { xc_add(&W.LX.word_compares, 1); if (f->buf2.n == 1 || pw_get(&f->buf2, f->buf2.n - 1) != pw_get(&f->buf, f->i)) pw_push(&f->buf2, pw_get(&f->buf, f->i)); f->i++; return; }
        f->ph = 3; push_intern_own(o, &f->buf2); return;
    case 3: fin(o, o->ret); return;
    }
}
static Frame fr_sort_own(uint64_t kind, Paged *w) { Frame f = fr(OF_SORT, kind, 0, 0, 0); paged_take(&f.buf, w); return f; }

/* LIST: a list record [K_LIST, words...] from buf (used for ordered atom lists) */
static void step_list(Op *o, Frame *f) { if (f->ph == 0) { f->ph = 1; push_intern_own(o, &f->buf); return; } fin(o, o->ret); }

/* ---------------------------------------------------------------- 4. demand (§60) ---- */

typedef struct { AtomId producer; uint64_t steps; bool alias; VEC(AtomId) occ; VEC(uint64_t) applies; } DNode;   /* applies: indices into graph applies */
typedef struct { uint64_t transform; int dir; MapId sigma; RefId arg; AtomId receiver; } DApply;
struct DGraph { VEC(DNode) nodes; VEC(AtomId) roots; VEC(DApply) applies; uint64_t rev; DGraphId id; /* the producer → node index is a record [K_MEMO, 0xD6, graph, producer] (side value = index + 1): a framed LOOKUP from a unit (§94) */ };
static uint64_t dgraph_rev(const DGraph *g) { return g->rev; }
/* producers and occurrences are paged (pushed one per unit); the public
 * readers materialize a contiguous view once, synchronously (outside the bounded API) */
typedef struct { Paged producers, occ; AtomId *pview; Occurrence *oview; } Demand;
typedef struct { SetId atoms; WorkCounts counts; } WorkSetInfo;

static DGraph *DG(DGraphId g) { require(rec_kind(g) == K_DGRAPH, "not a demand graph"); return (DGraph *)side(g)->ptr; }
DGraphId dgraph_new(void) {
    LOCK; static uint64_t seq; uint64_t w[2] = { K_DGRAPH, ++seq }; DGraphId g = intern_sync(w, 2, NULL);
    DGraph *d = pool_take(sizeof *d); d->id = g; side(g)->ptr = d; charge(FR_ALLOCATE_CHUNK); UNLOCK; return g;
}
static DNode *dnode(DGraph *d, AtomId p) { uint64_t k[4] = { K_MEMO, 0xD6, d->id, p }; xc_add(&W.LX.memo_lookup, 1); uint64_t id = find_sync(k, 4); if (!id || !side(id)->has_val) return NULL; return &d->nodes.data[side(id)->val - 1]; }   /* synchronous constructors only */
static DNode *dnode_at(DGraph *d, uint64_t ret) { return ret && side(ret)->has_val ? &d->nodes.data[side(ret)->val - 1] : NULL; }   /* from a framed LOOKUP's delivery */
static void push_dnode_lookup(Op *o, DGraph *d, AtomId p) { uint64_t k[4] = { K_MEMO, 0xD6, d->id, p }; push_lookup(o, k, 4); }
void dgraph_add_producer(DGraphId g, AtomId producer, uint64_t steps) {
    LOCK; DGraph *d = DG(g); require(!dnode(d, producer), "producer already in the graph");
    DNode n; memset(&n, 0, sizeof n); n.producer = producer; n.steps = steps; vec_push(&d->nodes, n);
    { uint64_t k[4] = { K_MEMO, 0xD6, g, producer }; uint64_t id = intern_sync(k, 4, NULL); side(id)->val = d->nodes.len; side(id)->has_val = true; }
    d->rev++; charge(FR_ALLOCATE_CHUNK); UNLOCK;
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
        if (!dm) { dm = pool_take(sizeof *dm); paged_init(&dm->producers, sizeof(AtomId)); paged_init(&dm->occ, sizeof(Occurrence)); f->acc4 = (uint64_t)(uintptr_t)dm; }
        if (f->i < nk) { uint64_t k[4] = { K_MARK, o->id, 1, K[f->i++] }; push_intern(o, k, 4); return; }
        f->i = 0; f->ph = 1; return;
    }
    case 1: {   /* root occurrences: the graph's root list (ordered) filtered to the requested roots set */
        if (f->i < d->roots.len) {
            AtomId r = d->roots.data[f->i];
            if (!set_has(f->b, r)) { f->i++; return; }
            Occurrence oc = { 0, f->i, r }; *(Occurrence *)paged_push(&dm->occ) = oc; charge(FR_ALLOCATE_CHUNK);
            uint64_t k[4] = { K_MARK, o->id, 1, r }; f->ph = 10; push_lookup(o, k, 4); return;
        }
        (void)R; f->ph = 2; return;
    }
    case 10: {  /* ready? → cut (the occurrence stays, the producer cone is not entered) */
        AtomId r = d->roots.data[f->i];
        if (o->ret) { xc_add(&W.LX.memo_hit, 1); f->i++; f->ph = 1; return; }
        uint64_t k[4] = { K_MARK, o->id, 2, r }; f->ph = 11; push_intern(o, k, 4); return;
    }
    case 11: {
        AtomId r = d->roots.data[f->i];
        Side *s = side(o->ret);
        if (!s->has_val) { s->has_val = true; pw_push(&f->buf, r); }
        f->i++; f->ph = 1; return;
    }
    case 2: {   /* pop */
        if (f->buf.n <= f->acc) { uint64_t w[5] = { K_DEMAND, f->a, f->b, f->c, dgraph_rev(d) }; f->ph = 6; push_intern(o, w, 5); return; }
        f->acc2 = pw_get(&f->buf, f->acc++);
        *(AtomId *)paged_push(&dm->producers) = f->acc2; charge(FR_ALLOCATE_CHUNK);
        f->j = 0; f->ph = 12; push_dnode_lookup(o, d, f->acc2); return;   /* the producer's node by the framed LOOKUP (§94) */
    }
    case 12: { DNode *n = dnode_at(d, o->ret); if (!n) { fail(o, "demanded producer has no recipe in the graph"); return; } f->acc3 = o->ret; f->ph = 3; return; }
    case 3: {   /* next occurrence of the popped producer */
        DNode *n = dnode_at(d, f->acc3);
        if (f->j >= n->occ.len) { f->ph = 2; return; }
        AtomId child = n->occ.data[f->j];
        Occurrence oc = { f->acc2, f->j, child }; *(Occurrence *)paged_push(&dm->occ) = oc; charge(FR_ALLOCATE_CHUNK);
        uint64_t k[4] = { K_MARK, o->id, 1, child }; f->ph = 4; push_lookup(o, k, 4); return;
    }
    case 4: {
        DNode *n = dnode_at(d, f->acc3); AtomId child = n->occ.data[f->j];
        if (o->ret) { xc_add(&W.LX.memo_hit, 1); f->j++; f->ph = 3; return; }           /* ready child: cut */
        uint64_t k[4] = { K_MARK, o->id, 2, child }; f->ph = 5; push_intern(o, k, 4); return;
    }
    case 5: {
        DNode *n = dnode_at(d, f->acc3); AtomId child = n->occ.data[f->j];
        Side *s = side(o->ret);
        if (!s->has_val) { s->has_val = true; pw_push(&f->buf, child); }
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
size_t demand_producers(DemandId d, const AtomId **out) {
    Demand *m = DM(d);
    if (!m->pview && m->producers.n) { m->pview = own(malloc(m->producers.n * sizeof(AtomId))); require(m->pview, "out of memory"); for (size_t i = 0; i < m->producers.n; i++) m->pview[i] = *(AtomId *)paged_at(&m->producers, i); }
    *out = m->pview; return m->producers.n;
}
size_t demand_occurrences(DemandId d, const Occurrence **out) {
    Demand *m = DM(d);
    if (!m->oview && m->occ.n) { m->oview = own(malloc(m->occ.n * sizeof(Occurrence))); require(m->oview, "out of memory"); for (size_t i = 0; i < m->occ.n; i++) m->oview[i] = *(Occurrence *)paged_at(&m->occ, i); }
    *out = m->oview; return m->occ.n;
}

/* EXTRACT: a = demand. ph0: occurrences (i): REQUEST then DELIVER atoms; ph1: producers (i): PUB, EVAL steps (j), applies (j2); ph2: sort + intern set */
static void step_extract(Op *o, Frame *f) {
    Demand *dm = DM(f->a); DGraph *d = DG(rec_w(f->a, 1));
    WorkSetInfo *wi = (WorkSetInfo *)(uintptr_t)f->acc4;
    if (!wi) { wi = pool_take(sizeof *wi); f->acc4 = (uint64_t)(uintptr_t)wi; }
    switch (f->ph) {
    case 0:
        if (f->i < dm->occ.n) {
            Occurrence oc = *(Occurrence *)paged_at(&dm->occ, f->i);
            uint64_t w[5] = { K_ATOM, f->j == 0 ? WK_REQUEST : WK_DELIVER, oc.owner, oc.slot, oc.child };
            f->ph = 20; push_intern(o, w, 5); return;
        }
        f->i = 0; f->j = 0; f->ph = 1; return;
    case 20:
        pw_push(&f->buf, o->ret);
        if (f->j == 0) { wi->counts.request++; f->j = 1; } else { wi->counts.deliver++; f->j = 0; f->i++; }
        f->ph = 0; return;
    case 1: {
        if (f->i >= dm->producers.n) { f->ph = 2; return; }
        AtomId p = *(AtomId *)paged_at(&dm->producers, f->i);
        if (!f->acc3) { f->ph = 24; push_dnode_lookup(o, d, p); return; }   /* the producer's node once per producer, by the framed LOOKUP (§94) */
        DNode *n = dnode_at(d, f->acc3);
        if (f->j == 0) { if (n->alias) { f->j = 1; return; } uint64_t w[3] = { K_ATOM, WK_PUB, p }; f->ph = 21; push_intern(o, w, 3); return; }   /* an alias publication ran no producer */
        if (f->j - 1 < n->steps) { uint64_t w[4] = { K_ATOM, WK_EVAL, p, f->j - 1 }; f->ph = 22; push_intern(o, w, 4); return; }
        size_t ka = f->j - 1 - n->steps;
        if (ka < n->applies.len) {
            DApply a = d->applies.data[n->applies.data[ka]];
            uint64_t w[8] = { K_ATOM, WK_APPLY, a.transform, (uint64_t)a.dir, a.sigma, a.arg, a.receiver, n->applies.data[ka] };
            f->ph = 23; push_intern(o, w, 8); return;
        }
        f->i++; f->j = 0; f->acc3 = 0; return;
    }
    case 24: if (!dnode_at(d, o->ret)) { fail(o, "demanded producer has no recipe in the graph"); return; } f->acc3 = o->ret; f->ph = 1; return;
    case 21: pw_push(&f->buf, o->ret); wi->counts.pub++; f->j++; f->ph = 1; return;
    case 22: pw_push(&f->buf, o->ret); wi->counts.eval++; f->j++; f->ph = 1; return;
    case 23: pw_push(&f->buf, o->ret); wi->counts.apply++; f->j++; f->ph = 1; return;
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
        case WK_PRODUCER: {   /* §94: each kernel call is a continuation stepped per unit (KERNEL); acc4 = t, acc3 = χ, acc2 = η, acc = environment */
            RefId src_ref = (RefId)side(f->a)->val; if (!src_ref) { fail(o, "producer identity without a representative reference"); return; }
            f->ph = 10; push(o, kfr(KK_REINDEX, src_ref, f->b, 0, 0)); return;
        }
        case WK_REQUEST: case WK_DELIVER:
            if (w[2]) { f->ph = 1; push(o, fr(OF_ATOMSPEC, w[2], f->b, 0, 0)); return; }
            f->acc = 0; f->ph = 2; push(o, fr(OF_ATOMSPEC, w[4], f->b, 0, 0)); return;
        case WK_PUB: case WK_EVAL: f->ph = 3; push(o, fr(OF_ATOMSPEC, w[2], f->b, 0, 0)); return;
        case WK_APPLY: f->ph = 4; push(o, fr(OF_ATOMSPEC, w[6], f->b, 0, 0)); return;
        default: fin(o, f->a); return;
        }
    case 10: f->acc4 = o->ret; f->ph = 11; push(o, kfr(KK_REF_VALIDATE, f->acc4, 0, 0, 0)); return;
    case 11: f->ph = 12; push(o, kfr(KK_FC_REINDEX, w[3], f->b, 0, 0)); return;
    case 12: f->acc3 = o->ret; f->ph = 13; push(o, kfr(KK_FC_PROJECT, f->acc3, f->acc4, 0, 0)); return;
    case 13: f->acc2 = o->ret; f->ph = 14; push(o, kfr(KK_ENTAILS, f->acc2, f->acc4, 0, 0)); return;
    case 14: f->ph = 15; push(o, kfr(KK_ENTRY_LOOKUP, f->acc4, f->acc2, 0, 0)); return;
    case 15: f->acc = rec_w(o->ret, 2); f->ph = 16; push(o, kfr(KK_SHAPE_OF, f->acc4, 0, 0, 0)); return;
    case 16: { uint64_t v[5] = { K_ATOM, WK_PRODUCER, o->ret, f->acc2, f->acc }; f->ph = 9; push_intern(o, v, 5); return; }
    case 1: f->acc = o->ret; f->ph = 2; push(o, fr(OF_ATOMSPEC, w[4], f->b, 0, 0)); return;
    case 2: { uint64_t v[5] = { K_ATOM, k, f->acc, w[3], o->ret }; f->ph = 9; push_intern(o, v, 5); return; }
    case 3: { uint64_t v[4] = { K_ATOM, k, o->ret, w[3] }; f->ph = 9; push_intern(o, v, k == WK_PUB ? 3 : 4); return; }
    case 4: f->acc = o->ret; f->ph = 17; push(o, kfr(KK_COMPOSE, w[4], f->b, 0, 0)); return;
    case 17: f->acc2 = o->ret; f->ph = 18; push(o, kfr(KK_REINDEX, w[5], f->b, 0, 0)); return;
    case 18: { uint64_t v[8] = { K_ATOM, WK_APPLY, w[2], w[3], f->acc2, o->ret, f->acc, w[7] }; f->ph = 9; push_intern(o, v, 8); return; }
    case 9: if (k == WK_PRODUCER && f->acc4 && !side(o->ret)->val) side(o->ret)->val = f->acc4; fin(o, o->ret); return;
    }
}
/* SPEC_SET: a = set, b = σ: image of every element, then sort/dedupe (the Boolean direct image s_!) */
static void step_spec_set(Op *o, Frame *f) {
    size_t n; const AtomId *S = set_atoms(f->a, &n);
    switch (f->ph) {
    case 0: if (f->i < n) { f->ph = 1; push(o, fr(OF_ATOMSPEC, S[f->i], f->b, 0, 0)); return; } f->ph = 2; return;
    case 1: pw_push(&f->buf, o->ret); f->i++; f->ph = 0; return;
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
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; }
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
        if (f->buf2.n < n) { size_t end = f->buf2.n + CHUNK_WORDS; if (end > n) end = n; while (f->buf2.n < end) pw_push(&f->buf2, 1); return; }
        f->i = 0; f->j = 0; f->ph = 1; return;
    case 1:
        if (f->i >= n) { f->ph = 3; f->i = 0; f->j = 0; f->acc = 0; return; }
        if (f->j >= n) { f->i++; f->j = 0; return; }
        if (f->j == f->i || !pw_get(&f->buf2, f->j) || !pw_get(&f->buf2, f->i)) { f->j++; return; }
        /* is buf[j] ⊆ buf[i]?  equal sets: keep the first (lower index) */
        if (pw_get(&f->buf, f->j) == pw_get(&f->buf, f->i)) { xc_add(&W.LX.word_compares, 1); if (f->j < f->i) pw_set(&f->buf2, f->i, 0); f->j++; return; }
        f->ph = 2; push(o, fr(OF_SUBSET, pw_get(&f->buf, f->j), pw_get(&f->buf, f->i), 0, 0)); return;
    case 2: if (o->ret == 1) pw_set(&f->buf2, f->i, 0); f->j++; f->ph = 1; return;
    case 3: {   /* survivor compaction, CHUNK_WORDS per unit: i scans, acc writes */
        if (f->i == 0 && f->acc == 0 && f->j == 0) { f->j = 1; }
        size_t end = f->i + CHUNK_WORDS; if (end > n) end = n;
        for (; f->i < end; f->i++) if (pw_get(&f->buf2, f->i)) pw_set(&f->buf, f->acc++, pw_get(&f->buf, f->i));
        if (f->i < n) return;
        paged_truncate(&f->buf, f->acc); f->ph = 4; push(o, fr_sort_own(K_FAMILY, &f->buf)); return;
    }
    case 4: fin(o, o->ret); return;
    }
}
/* FAMOP: a = 1 plus / 2 times, b = A, c = B */
static void step_famop(Op *o, Frame *f) {
    size_t na, nb; const SetId *A, *B; na = family_sets(f->b, &A); nb = family_sets(f->c, &B);
    switch (f->ph) {
    case 0:
        if (f->a == 1) {   /* plus: one member per unit (§94) */
            if (f->i < na) { pw_push(&f->buf, A[f->i++]); charge(FR_ALLOCATE_CHUNK); return; }
            if (f->j < nb) { pw_push(&f->buf, B[f->j++]); charge(FR_ALLOCATE_CHUNK); return; }
            f->ph = 3; return;
        }
        f->ph = 1; return;
    case 1:   /* pairwise unions */
        if (f->i >= na) { f->ph = 3; return; }
        if (f->j >= nb) { f->i++; f->j = 0; return; }
        f->ph = 2; push(o, fr(OF_SETOP, SO_UNION, A[f->i], B[f->j], 0)); return;
    case 2: pw_push(&f->buf, o->ret); f->j++; f->ph = 1; return;
    case 3: { Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); paged_take(&g.buf, &f->buf); f->ph = 4; push(o, g); return; }   /* ownership transfer, no copy (§94) */
    case 4: fin(o, o->ret); return;
    }
}
FamilyId family_make(size_t n, const SetId *sets) { LOCK; Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); pw_append(&g.buf, sets, n); FamilyId r = run_op(OF_NORMALIZE, PH_REWRITE, g, NULL); UNLOCK; return r; }
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
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; }
        if (formula_tag(F) == FM_ATOM) { uint64_t w[2] = { K_SET, formula_atom_of(F) }; f->ph = 5; push_intern(o, w, 2); return; }
        f->ph = 2; push(o, fr(OF_ANTICHAIN, formula_left(F), 0, 0, 0)); return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_ANTICHAIN, formula_right(F), 0, 0, 0)); return;
    case 3: f->ph = 6; push(o, fr(OF_FAMOP, formula_tag(F) == FM_OR ? 1 : 2, f->acc, o->ret, 0)); return;
    case 5: { Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); pw_push(&g.buf, o->ret); f->ph = 6; push(o, g); return; }
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
    for (size_t i = 0; i < na; i++) { SetId d = setop(SO_DIFF, A[i], k); Cost c = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, d, m, 0, 0), NULL); xc_add(&W.LX.limb_ops, 1); charge(FR_COST_COMPARE_CHUNK); if (cost_cmp(c, best) < 0) best = c; }
    free(A);
    UNLOCK; return best;
}
FamilyId family_specialize(FamilyId a, MapId sigma, const char **why) {
    LOCK; size_t na; const SetId *A0; na = family_sets(a, &A0); uint64_t *A = copy_words(A0, na);
    uint64_t *ids = na ? malloc(na * sizeof(uint64_t)) : NULL; require(!na || ids, "out of memory");
    for (size_t i = 0; i < na; i++) { ids[i] = run_op(OF_SPEC_SET, PH_PREPARE, fr(OF_SPEC_SET, A[i], sigma, 0, 0), why); if (!ids[i]) { free(ids); free(A); UNLOCK; return 0; } }
    free(A);
    Frame g = fr(OF_NORMALIZE, 0, 0, 0, 0); pw_append(&g.buf, ids, na); free(ids);
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
static Cost weight_locked(ModelId m, AtomId a) { uint64_t k[3] = { K_WEIGHT, m, a }; xc_add(&W.LX.memo_lookup, 1); uint64_t id = find_sync(k, 3); if (id && side(id)->has_val) { xc_add(&W.LX.memo_hit, 1); return side(id)->val; } return kind_weight(m, a); }
Cost model_weight(ModelId m, AtomId a) { LOCK; Cost c = weight_locked(m, a); UNLOCK; return c; }
SetId model_completed(ModelId m) { return rec_w(m, 10); }

/* ---- cost differences (§63) ---- */
typedef struct { NatDiff eps, masked; } CostDiffInfo;   /* exact signed differences of finite costs */
CostDiffId costdiff_make(SetId a, SetId b, SetId k, SetId c, ModelId m) {
    LOCK;
    SetId ak = setop(SO_DIFF, a, k), bk = setop(SO_DIFF, b, k);
    Cost ca = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, ak, m, 0, 0), NULL), cb = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, bk, m, 0, 0), NULL);
    SetId akc = setop(SO_DIFF, ak, c), bkc = setop(SO_DIFF, bk, c);
    Cost ma = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, akc, m, 0, 0), NULL), mb = run_op(OF_SUM, PH_REWRITE, fr(OF_SUM, bkc, m, 0, 0), NULL);
    xc_add(&W.LX.limb_ops, 2); charge(FR_COST_ADD_CHUNK); charge(FR_COST_ADD_CHUNK);
    uint64_t w[8] = { K_COSTDIFF, a, b, k, c, m, check_session_id(), global_env_version() };
    CostDiffId id = intern_sync(w, 8, NULL);
    if (!side(id)->ptr) { CostDiffInfo *in = pool_take(sizeof *in); require(cost_finite(ca) && cost_finite(cb) && cost_finite(ma) && cost_finite(mb), "a cost difference has finite premises"); in->eps = nat_diff(ca, cb); in->masked = nat_diff(ma, mb); side(id)->ptr = in; }
    UNLOCK; return id;
}
static int64_t diff_i64(NatDiff d) { uint64_t m; if (!nat_to_u64(d.magnitude, &m) || m > (uint64_t)INT64_MAX) return INT64_MIN; return d.sign < 0 ? -(int64_t)m : (int64_t)m; }
int64_t costdiff_epsilon(CostDiffId d) { return diff_i64(((CostDiffInfo *)side(d)->ptr)->eps); }
int64_t costdiff_masked(CostDiffId d) { return diff_i64(((CostDiffInfo *)side(d)->ptr)->masked); }
NatDiff costdiff_epsilon_exact(CostDiffId d) { return ((CostDiffInfo *)side(d)->ptr)->eps; }
NatDiff costdiff_masked_exact(CostDiffId d) { return ((CostDiffInfo *)side(d)->ptr)->masked; }
bool costdiff_current(CostDiffId d) { return rec_w(d, 6) == check_session_id() && rec_w(d, 7) == global_env_version(); }

/* ---------------------------------------------------------------- 6. typed records, preparation, realization (§66–§68.3) ---- */

BoundaryId boundary_make(ContextId ctx, FaceId face, size_t ninputs, const RefId *inputs, RefId type, uint64_t level, RefId continuation) {
    const char *why; uint64_t lv = 0; xc_add(&W.LX.kernel_calls, 1);
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
    xc_add(&W.LX.kernel_calls, 1);
    if (check(ctx, face, r, type, why) != CK_VALID) return 0;
    if (evidence) { xc_add(&W.LX.kernel_calls, 1); Inference q = infer(ctx, face, evidence); if (q.st != CK_VALID) { if (why) *why = q.reason ? q.reason : "connecting evidence does not type"; return 0; } }
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
/* Shared postorder boundary job. No recursive C traversal and no unchecked
 * cold lookup from PREPARE. Published expression syntax is immutable. */
static void step_boundary(Op *o, Frame *f) {
    ExprId e = f->a;
    Side *sd = side(e);
    BoundaryId out = 0;
    switch (f->ph) {
    case 0:
        if (sd->has_val) { fin(o, sd->val); return; }
        switch (expr_tag(e)) {
        case EX_EMPTY: out = rec_w(e, 2); break;
        case EX_PLAN: out = plan_boundary(rec_w(e, 2)); break;
        case EX_ALT: case EX_JOIN:
            f->ph = 1; push(o, fr(OF_BOUNDARY, rec_w(e, 2), 0, 0, 0)); return;
        }
        break;
    case 1:
        f->acc = o->ret; f->ph = 2;
        push(o, fr(OF_BOUNDARY, rec_w(e, 3), 0, 0, 0)); return;
    case 2: {
        BoundaryId l = f->acc, r = o->ret;
        if (expr_tag(e) == EX_ALT) out = l && l == r ? l : 0;
        else {
            ConnectorId g = rec_w(e, 4);
            if (l && r && g && rec_w(g, 1) == l && rec_w(g, 2) == r) out = rec_w(g, 3);
        }
        break;
    }
    default: die("invalid boundary frame phase");
    }
    sd->val = out; sd->has_val = true;
    fin(o, out);
}
BoundaryId expr_boundary(ExprId e) {
    LOCK;
    Side *sd = side(e);
    BoundaryId out = sd->has_val ? sd->val : run_op(OF_BOUNDARY, PH_PREPARE, fr(OF_BOUNDARY, e, 0, 0, 0), NULL);
    UNLOCK; return out;
}
/* Root-boundary completion has already visited both children of every
 * reachable ALT/JOIN, even when a child's boundary is invalid (zero). */
static BoundaryId prepared_boundary(ExprId e) {
    Side *sd = side(e); require(sd->has_val, "boundary requested before preparation"); return sd->val;
}
PlanId plan_specialize(PlanId p, MapId sigma, ContextId target, FaceId target_face, const char **why) {
    BoundaryId b = plan_boundary(p); size_t n; const uint64_t *bw = rec_words(b, &n);
    xc_add(&W.LX.kernel_calls, 1);
    if (check_map(target, target_face, sigma, bw[3], bw[4], why) != CK_VALID) return 0;
    RefId type = reindex(bw[5], sigma), cont = bw[7] ? reindex(bw[7], sigma) : 0; xc_add(&W.LX.kernel_calls, 2);
    size_t ni = bw[8]; RefId *in = ni ? malloc(ni * sizeof(RefId)) : NULL; require(!ni || in, "out of memory");
    for (size_t i = 0; i < ni; i++) { in[i] = reindex(bw[9 + i], sigma); xc_add(&W.LX.kernel_calls, 1); }
    BoundaryId nb = boundary_make(target, target_face, ni, in, type, bw[6], cont); free(in);
    if (!nb) { if (why) *why = "specialized boundary type does not form"; return 0; }
    RefId r = reindex(plan_reference(p), sigma), ev = plan_evidence(p) ? reindex(plan_evidence(p), sigma) : 0; xc_add(&W.LX.kernel_calls, 2);
    uint64_t *lst; size_t nl; { LOCK; const uint64_t *l0; nl = list_get(rec_w(p, 5), &l0); lst = nl ? malloc(nl * sizeof(uint64_t)) : NULL; require(!nl || lst, "out of memory"); if (nl) memcpy(lst, l0, nl * sizeof(uint64_t)); UNLOCK; }   /* copied: interning below may move the store */
    SetId img = set_specialize(plan_work(p), sigma, why); if (!img) { free(lst); return 0; }
    /* the ordered list of the image keeps first occurrences in the source order */
    AtomId *ord = nl ? malloc(nl * sizeof(AtomId)) : NULL; require(!nl || ord, "out of memory"); size_t m = 0;
    for (size_t i = 0; i < nl; i++) { SetId one; { AtomId a1 = lst[i]; one = set_make(1, &a1); } SetId s1 = set_specialize(one, sigma, why); if (!s1) { free(ord); free(lst); return 0; } AtomId a = set_atoms(s1, &n)[0]; bool seen = false; for (size_t k = 0; k < m; k++) { xc_add(&W.LX.word_compares, 1); if (ord[k] == a) seen = true; } if (!seen) ord[m++] = a; }
    free(lst);
    PlanId q = plan_make(nb, r, ev, m, ord, why); free(ord); return q;
}

/* ---------------------------------------------------------------- 7b. the framed proof-use audit (§88 in §94 units) ----
 * The dependency audit of §88.3–88.4 as engine operations: every unit is one
 * stored-syntax item, one framed lookup/intern, one set-union element or one
 * Tarjan edge. Symbol sets are K_SET records over symbol ids (sorted,
 * interned by the framed SORT/INTERN); node sets are memoized in
 * [K_MEMO, 0xA5, kind, id], a global's edge set in [K_MEMO, 0xA6, s, rev],
 * a verdict in [K_MEMO, 0xA7, G, face, e, E] whose value is the list
 * [K_LIST, status, assumptions, recursive, deps] (deps: [K_LIST, (s, rev)...]).
 * The traversal's "already on the stack" rule uses per-operation marks
 * [K_MARK, op, 5, kind, id]; discovery uses [K_MARK, op, 6, s]; Tarjan's
 * per-symbol state lives in the side of [K_MARK, op, 7, s] (val = index,
 * support = low, must = the symbol below it on Tarjan's stack, has_val =
 * on the stack). The synchronous `proof_use` (proof.c) computes the same
 * verdict by the same enumeration (`proof_node_item`). */
enum { AU_SYMS_MEMO = 0xA5, AU_EDGES_MEMO = 0xA6, AU_VERDICT_MEMO = 0xA7, AU_MARK_NODE = 5, AU_MARK_SEEN = 6, AU_MARK_TARJAN = 7 };
static void push_union(Op *o, SetId a, SetId b) { push(o, fr(OF_SETOP, SO_UNION, a, b, 0)); }

/* SYMS: a = node kind, b = node id. buf = children (kind, id pairs), buf2 = direct symbols; acc2 = accumulated set */
static void step_syms(Op *o, Frame *f) {
    switch (f->ph) {
    case 0: { if (f->a == N_CTX) { f->ph = 1; o->ret = 0; return; } uint64_t k[4] = { K_MEMO, AU_SYMS_MEMO, f->a, f->b }; f->ph = 1; push_lookup(o, k, 4); return; }   /* contexts are not memoized (as in proof.c) */
    case 1: {
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; }
        uint64_t k[5] = { K_MARK, o->id, AU_MARK_NODE, f->a, f->b }; f->ph = 2; push_lookup(o, k, 5); return;
    }
    case 2: {
        if (o->ret && side(o->ret)->has_val) { fin(o, W.EMPTY); return; }   /* active ancestor only */
        uint64_t k[5] = { K_MARK, o->id, AU_MARK_NODE, f->a, f->b }; f->ph = 3; push_intern(o, k, 5); return;
    }
    case 3: f->d = o->ret; side(f->d)->has_val = true; f->acc2 = W.EMPTY; f->i = 0; f->j = 0; f->ph = 4; return;
    case 4: {   /* one stored-syntax item per unit */
        if (f->i >= PN_SOURCES) { f->acc = 0; f->ph = 6; return; }
        PNodeItem it;
        if (!proof_node_item(f->a, f->b, (unsigned)f->i, f->j, &it)) { f->i++; f->j = 0; return; }
        f->j++;
        if (it.what == PN_CHILD) { pw_push(&f->buf, it.kind); pw_push(&f->buf, it.id); }
        else if (it.what == PN_SYMBOL) pw_push(&f->buf2, it.id);
        return;
    }
    case 6:   /* children, one request each; then the direct symbols */
        if (f->acc + 1 < f->buf.n) { uint64_t ck = pw_get(&f->buf, f->acc), cid = pw_get(&f->buf, f->acc + 1); f->acc += 2; f->ph = 7; push(o, fr(OF_SYMS, ck, cid, 0, 0)); return; }
        f->ph = 8; push(o, fr_sort_own(K_SET, &f->buf2)); return;
    case 7: f->ph = 9; push_union(o, f->acc2, o->ret); return;
    case 9: f->acc2 = o->ret; f->ph = 6; return;
    case 8: f->ph = 10; push_union(o, f->acc2, o->ret); return;
    case 10: { side(f->d)->has_val = false; f->acc2 = o->ret; if (f->a == N_CTX) { fin(o, f->acc2); return; } uint64_t k[4] = { K_MEMO, AU_SYMS_MEMO, f->a, f->b }; f->ph = 11; push_intern(o, k, 4); return; }
    case 11: { Side *s = side(o->ret); s->val = f->acc2; s->has_val = true; fin(o, f->acc2); return; }
    }
}
/* EDGES: a = symbol. c = its revision; acc2 = accumulated set; i = source cursor (0 type, 1 body, 2+k parameter k) */
static void step_edges(Op *o, Frame *f) {
    SymbolId s = f->a;
    switch (f->ph) {
    case 0: { f->c = global_revision(s); uint64_t k[4] = { K_MEMO, AU_EDGES_MEMO, s, f->c }; f->ph = 1; push_lookup(o, k, 4); return; }
    case 1: if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; } f->acc2 = W.EMPTY; f->i = 0; f->ph = 2; return;
    case 2: {
       
        if (f->i == 0) { f->ph = 3; push(o, fr(OF_SYMS, N_REF, global_type(s), 0, 0)); return; }
        if (f->i == 1) { RefId body = global_body(s); if (!body) { f->i++; return; } f->ph = 3; push(o, fr(OF_SYMS, N_REF, body, 0, 0)); return; }
        size_t n; const uint64_t *params = varset_get(global_params(s), &n); size_t k = f->i - 2;
        if (k >= n) { uint64_t key[4] = { K_MEMO, AU_EDGES_MEMO, s, f->c }; f->ph = 4; push_intern(o, key, 4); return; }
        f->ph = 3; push(o, fr(OF_SYMS, N_REF, term_var_type(params[k]), 0, 0)); return;
    }
    case 3: f->ph = 5; push_union(o, f->acc2, o->ret); return;
    case 5: f->acc2 = o->ret; f->i++; f->ph = 2; return;
    case 4: { Side *sd = side(o->ret); sd->val = f->acc2; sd->has_val = true; fin(o, f->acc2); return; }
    }
}
/* AUDIT: a = Γ, b = φ, c = e, d = E. Result: the verdict list record.
 * buf = discovery worklist, then Tarjan's call stack (s, k, edges triples);
 * buf2 = assumptions, then cyclic members; buf3 = [K_LIST, (s, rev)...] deps.
 * acc = verdict / Tarjan root cursor, acc2 = roots set / assumptions set,
 * acc3 = current symbol, acc4 = recursive set, e = edges set / next index */
static Side *tarjan_side(uint64_t ret) { return ret ? side(ret) : NULL; }
static void step_audit(Op *o, Frame *f) {
    switch (f->ph) {
    /* The same prerequisites as proof_use, before even a false-face or
     * cached verdict. Each is one separately charged opaque kernel call;
     * these calls remain in the already-open kernel-lowering obligation. */
    case 0: f->ph = 50; push(o, kfr(KK_ADMISSION, 0, 0, 0, 0)); return;                    /* each prerequisite a kernel continuation (§94); a rejection fails this job with the kernel's diagnostic */
    case 50: f->ph = 51; push(o, kfr(KK_CONTEXT, f->a, 0, 0, 0)); return;
    case 51: f->ph = 52; push(o, kfr(KK_IS_TYPE, f->a, f->b, f->d, 0)); return;
    case 52: f->ph = 53; push(o, kfr(KK_CHECK, f->a, f->b, f->c, f->d)); return;
    case 53: {
        if (fc_is_false(f->b)) { uint64_t v[5] = { K_LIST, PU_CORE, W.EMPTY, W.EMPTY, 0 }; f->ph = 30; push_intern(o, v, 5); return; }   /* vacuous: a judgment under the false face is local to that face */
        uint64_t k[6] = { K_MEMO, AU_VERDICT_MEMO, f->a, f->b, f->c, f->d }; f->ph = 1; push_lookup(o, k, 6); return;
    }
    case 30: fin(o, o->ret); return;
    case 1: if (o->ret && side(o->ret)->has_val) { f->acc = side(o->ret)->val; f->i = 0; f->ph = 2; return; } f->ph = 3; return;
    case 2: {   /* a cached verdict is reused while every recorded revision is current: one dependency per unit */
        const uint64_t *l; size_t n = rec_w(f->acc, 4) ? list_get(rec_w(f->acc, 4), &l) : 0;
        if (f->i + 1 < n) { if (global_revision(l[f->i]) != l[f->i + 1]) { f->ph = 3; return; } f->i += 2; return; }
        xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, f->acc); return;
    }
    /* roots: the context declarations, the expected type, the evidence */
    case 3: f->ph = 4; push(o, fr(OF_SYMS, N_CTX, f->a, 0, 0)); return;
    case 4: f->acc2 = o->ret; f->ph = 5; push(o, fr(OF_SYMS, N_REF, f->d, 0, 0)); return;
    case 5: f->ph = 6; push_union(o, f->acc2, o->ret); return;
    case 6: f->acc2 = o->ret; f->ph = 7; push(o, fr(OF_SYMS, N_REF, f->c, 0, 0)); return;
    case 7: f->ph = 8; push_union(o, f->acc2, o->ret); return;
    case 8: f->acc2 = o->ret; f->i = 0; pw_push(&f->buf3, K_LIST); f->ph = 9; return;
    case 9: { size_t n; const AtomId *R = set_atoms(f->acc2, &n); if (f->i < n) { pw_push(&f->buf, R[f->i++]); return; } f->ph = 10; return; }   /* the worklist, one root per unit */
    /* discovery */
    case 10: {
        if (!f->buf.n) { f->ph = 20; return; }
        f->acc3 = pw_get(&f->buf, f->buf.n - 1); paged_pop(&f->buf);
        uint64_t k[4] = { K_MARK, o->id, AU_MARK_SEEN, f->acc3 }; f->ph = 11; push_lookup(o, k, 4); return;
    }
    case 11: { if (o->ret) { f->ph = 10; return; } uint64_t k[4] = { K_MARK, o->id, AU_MARK_SEEN, f->acc3 }; f->ph = 12; push_intern(o, k, 4); return; }
    case 12: {
        SymbolId s = f->acc3;
        pw_push(&f->buf3, s); pw_push(&f->buf3, global_revision(s));
        if (!global_body(s)) pw_push(&f->buf2, s);
        f->ph = 13; push(o, fr(OF_EDGES, s, 0, 0, 0)); return;
    }
    case 13: f->e = o->ret; f->j = 0; f->ph = 14; return;
    case 14: { size_t n; const AtomId *E = set_atoms(f->e, &n); if (f->j < n) { uint64_t k[4] = { K_MARK, o->id, AU_MARK_SEEN, E[f->j] }; f->ph = 15; push_lookup(o, k, 4); return; } f->ph = 10; return; }
    case 15: { size_t n; const AtomId *E = set_atoms(f->e, &n); if (!o->ret) pw_push(&f->buf, E[f->j]); f->j++; f->ph = 14; return; }
    /* the assumptions set, then Tarjan's components over the reached symbols (deps order) */
    case 20: f->ph = 21; push(o, fr_sort_own(K_SET, &f->buf2)); return;
    case 21: f->acc2 = o->ret; f->acc = 1; f->e = 0; f->i = 0; f->ph = 22; return;    /* acc = cursor over buf3 pairs (from 1); e = next index; i = Tarjan's stack top (0: empty); buf2 now collects cyclic members */
    case 22: {   /* next unvisited root */
        if (f->acc + 1 >= f->buf3.n) { f->ph = 40; return; }
        f->acc3 = pw_get(&f->buf3, f->acc); f->acc += 2;
        uint64_t k[4] = { K_MARK, o->id, AU_MARK_TARJAN, f->acc3 }; f->ph = 23; push_lookup(o, k, 4); return;
    }
    case 23: { if (o->ret && side(o->ret)->val) { f->ph = 22; return; } uint64_t k[4] = { K_MARK, o->id, AU_MARK_TARJAN, f->acc3 }; f->ph = 24; push_intern(o, k, 4); return; }
    case 24: {   /* visit root: index = low = ++next; onto the stack; call frame (s, 0, edges) */
        Side *sd = side(o->ret); sd->val = sd->support = ++f->e; sd->must = f->i; f->i = f->acc3; sd->has_val = true;   /* index, low, stack link (the symbol below), on-stack */
        pw_push(&f->buf, f->acc3); pw_push(&f->buf, 0); f->ph = 25; push(o, fr(OF_EDGES, f->acc3, 0, 0, 0)); return;
    }
    case 25: pw_push(&f->buf, o->ret); f->ph = 26; return;
    case 26: {   /* one edge of the top call frame per unit */
        if (f->buf.n < 3) { f->ph = 22; return; }
        SymbolId s = pw_get(&f->buf, f->buf.n - 3); uint64_t k = pw_get(&f->buf, f->buf.n - 2); SetId es = pw_get(&f->buf, f->buf.n - 1);
        size_t m; const AtomId *E = set_atoms(es, &m);
        if (k < m) { pw_set(&f->buf, f->buf.n - 2, k + 1); f->acc3 = E[k]; uint64_t key[4] = { K_MARK, o->id, AU_MARK_TARJAN, f->acc3 }; f->ph = 27; push_lookup(o, key, 4); return; }
        /* all edges done: s's own state */
        uint64_t key[4] = { K_MARK, o->id, AU_MARK_TARJAN, s }; f->ph = 31; push_lookup(o, key, 4); return;
    }
    case 27: {   /* edge s → d */
        Side *d = tarjan_side(o->ret);
        if (!d || !d->val) { uint64_t key[4] = { K_MARK, o->id, AU_MARK_TARJAN, f->acc3 }; f->ph = 28; push_intern(o, key, 4); return; }   /* unvisited: descend */
        if (d->has_val) { f->acc4 = d->val; uint64_t key[4] = { K_MARK, o->id, AU_MARK_TARJAN, pw_get(&f->buf, f->buf.n - 3) }; f->ph = 29; push_lookup(o, key, 4); return; }   /* on the stack: low[s] = min(low[s], index[d]) */
        f->ph = 26; return;
    }
    case 28: { Side *d = side(o->ret); d->val = d->support = ++f->e; d->must = f->i; f->i = f->acc3; d->has_val = true; pw_push(&f->buf, f->acc3); pw_push(&f->buf, 0); f->ph = 25; push(o, fr(OF_EDGES, f->acc3, 0, 0, 0)); return; }
    case 29: { Side *s = side(o->ret); if (f->acc4 < s->support) s->support = f->acc4; f->ph = 26; return; }
    case 31: {   /* s finished its edges: a component root pops the stack down to s; then the parent's low */
        Side *s = side(o->ret); f->acc4 = o->ret;
        if (s->support == s->val) { pw_set(&f->buf, f->buf.n - 2, f->buf2.n); f->ph = 32; return; }   /* the call frame's cursor slot now records where this component's members start in buf2 */
        f->ph = 35; return;
    }
    case 32: {   /* pop one member per unit: the symbol on top of Tarjan's stack */
        SymbolId top = f->i; uint64_t key[4] = { K_MARK, o->id, AU_MARK_TARJAN, top }; f->acc3 = top; f->ph = 33; push_lookup(o, key, 4); return;
    }
    case 33: {
        Side *d = side(o->ret); d->has_val = false; f->i = d->must;   /* off the stack; the stack top moves down */
        pw_push(&f->buf2, f->acc3);                                     /* a provisional member */
        SymbolId s = pw_get(&f->buf, f->buf.n - 3);
        if (f->acc3 != s) { f->ph = 32; return; }
        f->j = 0; f->ph = 34; return;   /* the component is complete: cyclic iff more than one member or a self-edge */
    }
    case 34: {   /* self-edge scan, one edge per unit; then keep or drop the provisional members */
        SymbolId s = pw_get(&f->buf, f->buf.n - 3); size_t m; const AtomId *E = set_atoms(pw_get(&f->buf, f->buf.n - 1), &m);
        size_t start = pw_get(&f->buf, f->buf.n - 2), members = f->buf2.n - start;
        bool cyclic = members > 1;
        if (!cyclic && f->j < m) { if (E[f->j] == s) cyclic = true; else { f->j++; return; } }
        if (!cyclic) paged_truncate(&f->buf2, start);   /* an acyclic singleton is not recursive */
        f->ph = 35; return;
    }
    case 35: {   /* pop the call frame; parent.low = min(parent.low, low[s]) */
        Side *s = side(f->acc4); uint64_t low = s->support;
        paged_pop(&f->buf); paged_pop(&f->buf); paged_pop(&f->buf);
        if (f->buf.n < 3) { f->ph = 22; return; }
        f->acc4 = low; uint64_t key[4] = { K_MARK, o->id, AU_MARK_TARJAN, pw_get(&f->buf, f->buf.n - 3) }; f->ph = 36; push_lookup(o, key, 4); return;
    }
    case 36: { Side *p = side(o->ret); if (f->acc4 < p->support) p->support = f->acc4; f->ph = 26; return; }
    /* the verdict */
    case 40: f->ph = 41; push(o, fr_sort_own(K_SET, &f->buf2)); return;
    case 41: { f->acc4 = o->ret; Frame g = fr(OF_LIST, 0, 0, 0, 0); paged_take(&g.buf, &f->buf3); f->ph = 42; push(o, g); return; }
    case 42: {
        size_t na, nr; set_atoms(f->acc2, &na); set_atoms(f->acc4, &nr);
        uint64_t st = nr ? PU_PENDING : na ? PU_ASSUMED : PU_CORE;
        uint64_t v[5] = { K_LIST, st, f->acc2, f->acc4, o->ret }; f->ph = 43; push_intern(o, v, 5); return;
    }
    case 43: { f->acc = o->ret; uint64_t k[6] = { K_MEMO, AU_VERDICT_MEMO, f->a, f->b, f->c, f->d }; f->ph = 44; push_intern(o, k, 6); return; }
    case 44: { Side *s = side(o->ret); s->val = f->acc; s->has_val = true; fin(o, f->acc); return; }
    }
}


/* ---------------------------------------------------------------- 7c. kernel calls as continuations (§94, kcont.h) ----
 * KERNEL: a = kind, b/c/d/e = operands. The call runs on its own continuation
 * (a thread whose stack is the retained continuation); a unit grants it
 * W.grant transitions — one under op_step(h, 1), the whole run under the
 * synchronous drivers — and the transitions taken are the units charged
 * (FR_KERNEL_TRANSITION). Exactly one continuation is in progress at a time:
 * a kernel frame whose continuation cannot start advances the active one by
 * its grant instead (a frame that meets a relocation another job began
 * advances it, §94.2(4)), so progress is never withheld. The job's result is
 * published only when the call has completed. */
static void kernel_call(KCont *k) {
    const char *why = NULL; uint64_t level = 0;
    switch (k->arg[0]) {
    case KK_REINDEX: k->out[0] = reindex(k->arg[1], k->arg[2]); k->ok = true; break;
    case KK_COMPOSE: k->out[0] = compose(k->arg[1], k->arg[2]); k->ok = true; break;
    case KK_FC_REINDEX: k->out[0] = fc_reindex(k->arg[1], k->arg[2]); k->ok = true; break;
    case KK_REF_VALIDATE: k->ok = ref_validate(k->arg[1], &why); k->why = k->ok ? "" : "specialized reference fails structural validation"; break;
    case KK_FC_PROJECT: { size_t n; const uint64_t *S = dimset_get(ref_support(k->arg[2]), &n); k->out[0] = fc_project(k->arg[1], S, n); k->ok = true; break; }
    case KK_ENTAILS: k->ok = fc_entails(k->arg[1], ref_required(k->arg[2])); k->why = k->ok ? "" : "specialized occurrence outside its required face"; break;
    case KK_ENTRY_LOOKUP: { EntryId e = eval_entry_lookup(k->arg[1], k->arg[2]); k->out[0] = e; k->out[1] = e ? eval_entry_env(e) : global_env_version(); k->ok = true; break; }
    case KK_SHAPE_OF: k->out[0] = shape_of(k->arg[1]); k->ok = true; break;
    case KK_INFER: { Inference q = infer(k->arg[1], k->arg[2], k->arg[3]); k->out[0] = q.type; k->out[1] = q.st; k->ok = q.st == CK_VALID;
        k->outcome = q.st == CK_VALID ? KO_OK : q.st == CK_INVALID ? KO_INVALID : KO_UNRESOLVED;
        k->why = q.st == CK_VALID ? "" : q.st == CK_INVALID ? "proof use INVALID: connecting evidence does not type in its occurrence context" : "proof use UNRESOLVED: connecting evidence could not be checked in this attempt"; break; }
    case KK_ADMISSION: case KK_CONTEXT: case KK_IS_TYPE: case KK_CHECK: {
        CheckStatus st = k->arg[0] == KK_ADMISSION ? check_admission(&why) : k->arg[0] == KK_CONTEXT ? check_context(k->arg[1], &why)
                       : k->arg[0] == KK_IS_TYPE ? check_is_type(k->arg[1], k->arg[2], k->arg[3], &level, &why) : check(k->arg[1], k->arg[2], k->arg[3], k->arg[4], &why);
        k->out[0] = level; k->out[1] = st; k->ok = st == CK_VALID;
        k->outcome = st == CK_VALID ? KO_OK : st == CK_INVALID ? KO_INVALID : KO_UNRESOLVED;
        k->why = st == CK_VALID ? "" : st == CK_INVALID ? "proof use INVALID: judgment prerequisite rejected" : "proof use UNRESOLVED: judgment prerequisite unresolved in this attempt"; break;
    }
    case KK_TRANSFORM_EVIDENCE: { ContextId G; FaceId face; RefId e, E; k->ok = transform_evidence(k->arg[1], &G, &face, &e, &E);
        if (k->ok) { k->out[0] = G; k->out[1] = face; k->out[2] = e; k->out[3] = E; } else k->why = "proof use INVALID: connecting evidence does not type in its occurrence context"; break; }
    case KK_NAT: {   /* exact cost arithmetic: one transition per limb (nat.c) */
        Cost a = k->arg[2], b = k->arg[3];
        k->out[0] = k->arg[1] == CA_ADD ? cost_sum(a, b) : k->arg[1] == CA_MIN ? (cost_cmp(a, b) <= 0 ? a : b) : (uint64_t)(cost_cmp(a, b) + 1);
        k->ok = true; break;
    }
    default: k->ok = false; k->why = "unknown kernel call"; break;
    }
}
static void kernel_grant(KCont *k) {
    W.kc_active = k; W.kc_owner = k->job;
    size_t used = kc_grant(k, W.grant ? W.grant : 1);
    if (used > 1) { W.extra += used - 1; xc_add(&W.LX.frames[FR_KERNEL_TRANSITION], used - 1); xc_add(&W.LX.by_phase[W.phase], used - 1); }
}
static Frame kfr(uint64_t kind, uint64_t b, uint64_t c, uint64_t d, uint64_t e) { Frame f = fr(OF_KERNEL, kind, b, c, d); f.e = e; return f; }
/* BOUNDS-COMPLETION §3: cost arithmetic in units. Immediate operands (and
 * INFINITY) take one bounded word operation in this unit; boxed operands
 * request the shared NAT job — a kernel continuation keyed by the operation
 * and its immutable operands, one transition per limb — and the frame
 * resumes at `resume` with the result in o->ret. True when *out holds the
 * result now (the caller then continues at `resume` itself). */
static bool cost_op(Op *o, Frame *f, int kind, Cost a, Cost b, uint16_t resume, Cost *out) {
    xc_add(&W.LX.limb_ops, 1);
    bool small = (a == COST_INF || nat_is_small(a)) && (b == COST_INF || nat_is_small(b));
    if (small) {
        if (kind == CA_ADD) { *out = cost_sum(a, b); return true; }   /* two immediates: one word addition (a carry past 2^63 boxes one limb) */
        int c = cost_cmp(a, b); *out = kind == CA_MIN ? (c <= 0 ? a : b) : (uint64_t)(c + 1); return true;
    }
    f->ph = resume; push(o, kfr(KK_NAT, kind, a, b, 0)); return false;
}
static void step_kernel(Op *o, Frame *f) {
    switch (f->ph) {
    case 0: {
        uint64_t args[6] = { f->a, f->b, f->c, f->d, f->e, 0 };
        KCont *k = kc_new(kernel_call, args, 5); k->job = o->id; k->acct = reuse_scope_new(W.phase);
        f->acc = (uint64_t)(uintptr_t)k;
        xc_add(&W.LX.kernel_calls, 1);
        f->ph = 1;
    }
    /* fall through */
    case 1: {
        KCont *k = (KCont *)(uintptr_t)f->acc;
        if (!kc_done(k)) kernel_grant(k);
        if (!kc_done(k)) {
            /* the same frame, retained: resumed by the next unit. A continuation
             * that waits for another continuation names it: this job then waits
             * on that job (a represented dependency the scheduler drives) */
            if (k->blocked && k->blocked_job && k->blocked_job != o->id) {
                Op *dep = JOB(k->blocked_job);
                if (dep->st == OP_RUNNING) { o->waiting_on = dep->id; o->kwait = true; }   /* V21 R2: a predicate wait, revalidated after each unit of the dependency */
            }
            return;
        }
        reuse_scope_close(k->acct); reuse_scope_unref(k->acct);   /* every event of the call is charged once */
        KOutcome oc = k->outcome; uint64_t out[4] = { k->out[0], k->out[1], k->out[2], k->out[3] }; const char *why = k->why;
        if (W.kc_active == k) { W.kc_active = NULL; W.kc_owner = 0; }
        kc_free(k); f->acc = 0;
        if (oc == KO_UNRESOLVED) { o->unresolved = check_attempt(); fail(o, why); return; }   /* attempt-local: retried by a request in a later attempt */
        if (oc != KO_OK) { fail(o, why); return; }                                           /* settled */
        switch (f->a) {
        case KK_ENTRY_LOOKUP: f->acc3 = out[1]; f->ph = 2; { uint64_t lw[3] = { K_LIST, out[0], out[1] }; push_intern(o, lw, 3); } return;   /* (entry, environment) as a list record */
        case KK_TRANSFORM_EVIDENCE: { uint64_t lw[5] = { K_LIST, out[0], out[1], out[2], out[3] }; f->ph = 2; push_intern(o, lw, 5); return; }
        case KK_REF_VALIDATE: case KK_ENTAILS: case KK_ADMISSION: case KK_CONTEXT: case KK_CHECK: fin(o, 1); return;
        default: fin(o, out[0]); return;   /* REINDEX, COMPOSE, FC_REINDEX, FC_PROJECT, SHAPE_OF, INFER (the type), IS_TYPE (the level) */
        }
    }
    case 2: fin(o, o->ret); return;
    }
}

/* PREPARE: a = expr, b = model. buf = node stack, buf2 = atom order, buf3 = hypotheses.
 * ph0 pop/validate/push children; ph7–9 atom order loop over the node's
 * ordered work list; ph2 formula; ph3 F_K; ph4 order list; ph5 problem record.
 * ph14 copies an ASSUMED audit's assumptions into buf3 one per unit (d = source,
 * e = remaining, c = the phase to resume); ph18 is a JOIN's second audit. */
/* §88.4 in units: infer/extract supplies the evidence judgment, then
 * shared AUDIT checks all proof_use prerequisites before the dependency walk; the
 * verdict list is read at ph 16 — CORE continues, ASSUMED copies the
 * assumptions set one symbol per unit (ph 14), PENDING fails. c = the phase
 * to resume, d = the assumptions set, e = its cursor. */
/* the evidence judgment: INFER (ph 19 plan / 21 connector reference) and
 * TRANSFORM_EVIDENCE (ph 20) are kernel continuations; their delivery
 * requests the shared AUDIT */
static void plan_judgment(Frame *f, ContextId *ctx, FaceId *face, RefId *ev) { PlanId p = rec_w(f->acc3, 2); size_t n; const uint64_t *bw = rec_words(plan_boundary(p), &n); *ctx = bw[3]; *face = bw[4]; *ev = plan_evidence(p); }
static void join_judgment(Frame *f, ContextId *ctx, FaceId *face, RefId *ev) { ConnectorId g = rec_w(f->acc3, 4); size_t n; const uint64_t *bw = rec_words(rec_w(g, 3), &n); *ctx = bw[3]; *face = bw[4]; *ev = rec_w(g, 5); }
static void step_prepare(Op *o, Frame *f) {
    switch (f->ph) {
    case 0: {
        if (f->acc == 0) { f->ph = 10; push(o, fr(OF_BOUNDARY, f->a, 0, 0, 0)); return; }
        if (!f->buf.n) { f->ph = 2; push(o, fr(OF_EXPRF, f->a, 0, 0, 0)); return; }
        ExprId e = pw_get(&f->buf, f->buf.n - 1); paged_pop(&f->buf);
        f->acc3 = e; f->ph = 1; return;
    }
    case 10:
        f->acc2 = o->ret;
        if (!f->acc2) { fail(o, "expression has no common complete boundary"); return; }
        pw_push(&f->buf, f->a); pw_push(&f->buf2, K_LIST);
        f->acc = 1; f->ph = 0; return;
    case 1: {   /* VALIDATE_PREPARED_BOUNDARY */
        ExprId e = f->acc3; ExprTag t = expr_tag(e);
        if (prepared_boundary(e) != f->acc2 && t != EX_JOIN) { fail(o, "alternative at a different boundary"); return; }
        f->acc4 = 0; f->i = 0; f->e = 0;   /* ordered atom list to scan; no assumptions pending */
        switch (t) {
        case EX_EMPTY: f->ph = 7; return;
        case EX_PLAN: {
            PlanId p = rec_w(e, 2); f->acc4 = rec_w(p, 5);
            if (plan_evidence(p)) { ContextId ctx; FaceId face; RefId ev; plan_judgment(f, &ctx, &face, &ev); f->ph = 19; push(o, kfr(KK_INFER, ctx, face, ev, 0)); return; }
            f->ph = 7; return;
        }
        case EX_ALT: pw_push(&f->buf, rec_w(e, 3)); pw_push(&f->buf, rec_w(e, 2)); f->ph = 7; return;
        case EX_JOIN: {
            ConnectorId g = rec_w(e, 4); BoundaryId l = prepared_boundary(rec_w(e, 2)), r = prepared_boundary(rec_w(e, 3));
            if (!g) { fail(o, "composition without a connector"); return; }
            if (rec_w(g, 1) != l || rec_w(g, 2) != r) { fail(o, "incompatible composition: connector interfaces differ from the composed boundaries"); return; }
            if (rec_w(g, 3) != f->acc2 && prepared_boundary(e) != f->acc2) { fail(o, "composition result at a different boundary"); return; }
            if (!rec_w(g, 4) && !rec_w(g, 5)) { fail(o, "connector without connecting evidence"); return; }
            if (!rec_w(g, 7)) { fail(o, "connector without its work set"); return; }
            pw_push(&f->buf, rec_w(e, 3)); pw_push(&f->buf, rec_w(e, 2));
            f->acc4 = rec_w(g, 7);
            if (rec_w(g, 4)) { f->ph = 20; push(o, kfr(KK_TRANSFORM_EVIDENCE, rec_w(g, 4), 0, 0, 0)); return; }
            f->ph = 18; return;
        }
        }
        return;
    }
    case 18: {   /* a JOIN's reference evidence, after its transform evidence */
        ExprId e = f->acc3; ConnectorId g = rec_w(e, 4);
        if (rec_w(g, 5)) { ContextId ctx; FaceId face; RefId ev; join_judgment(f, &ctx, &face, &ev); f->ph = 21; push(o, kfr(KK_INFER, ctx, face, ev, 0)); return; }
        f->ph = 7; return;
    }
    case 19: { ContextId ctx; FaceId face; RefId ev; plan_judgment(f, &ctx, &face, &ev); f->c = 7; f->ph = 16; push(o, fr(OF_AUDIT, ctx, face, ev, o->ret)); return; }
    case 21: { ContextId ctx; FaceId face; RefId ev; join_judgment(f, &ctx, &face, &ev); f->c = 7; f->ph = 16; push(o, fr(OF_AUDIT, ctx, face, ev, o->ret)); return; }
    case 20: { const uint64_t *l; list_get(o->ret, &l); f->c = 18; f->ph = 16; push(o, fr(OF_AUDIT, l[0], l[1], l[2], l[3])); return; }
    case 16: {   /* the verdict */
        uint64_t v = o->ret; charge(FR_PROOF_USE_AUDIT);
        switch ((ProofUseStatus)rec_w(v, 1)) {
        case PU_CORE: f->ph = (uint16_t)f->c; f->c = 0; return;
        case PU_ASSUMED: f->d = rec_w(v, 2); f->e = 0; f->ph = 14; return;
        default: fail(o, "proof use PENDING: connecting evidence depends on a recursive declaration component and has no logical witness yet"); return;
        }
    }
    case 14: {   /* one assumption symbol per unit into the hypotheses buffer (§94) */
        size_t n; const AtomId *A = set_atoms(f->d, &n);
        if (f->e < n) { pw_push(&f->buf3, A[f->e++]); charge(FR_ALLOCATE_CHUNK); return; }
        f->d = 0; f->ph = (uint16_t)f->c; f->c = 0; return;
    }
    case 7: {
        if (!f->acc4) { f->ph = 0; return; }
        const uint64_t *l; size_t n = list_get(f->acc4, &l);
        if (f->i >= n) { f->ph = 0; return; }
        uint64_t k[4] = { K_MARK, o->id, 4, l[f->i] }; f->ph = 8; push_lookup(o, k, 4); return;
    }
    case 8: {
        if (o->ret) { xc_add(&W.LX.memo_hit, 1); f->i++; f->ph = 7; return; }
        const uint64_t *l; list_get(f->acc4, &l);
        uint64_t k[4] = { K_MARK, o->id, 4, l[f->i] }; f->ph = 9; push_intern(o, k, 4); return;
    }
    case 9: { const uint64_t *l; list_get(f->acc4, &l); pw_push(&f->buf2, l[f->i]); f->i++; f->ph = 7; return; }
    case 2: f->acc3 = o->ret; f->ph = 3; push(o, fr(OF_SUBST, f->acc3, model_completed(f->b), 1, 0)); return;
    case 3: { f->acc4 = o->ret; Frame g = fr(OF_LIST, 0, 0, 0, 0); paged_take(&g.buf, &f->buf2); f->ph = 4; push(o, g); return; }   /* no copy: ownership transfer (§94) */
    case 4: f->acc = o->ret; f->ph = 6; push(o, fr_sort_own(K_SET, &f->buf3)); return;   /* the hypotheses set by the framed SORT (one sift / one dedupe element per unit) and its INTERN; no sort or copy inside the unit (§94) */
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
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; }
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
typedef struct { Paged plans, conns; PlanId *plview; ConnectorId *cview; SetId work; Cost cost; SetId support; } Real;   /* paged (pushed/rolled back one per unit); contiguous views materialized by the public readers */
static void step_realize(Op *o, Frame *f) {
    Real *R = (Real *)(uintptr_t)f->acc4;
    switch (f->ph) {
    case 0: {
        if (!R) { R = pool_take(sizeof *R); paged_init(&R->plans, sizeof(PlanId)); paged_init(&R->conns, sizeof(ConnectorId)); f->acc4 = (uint64_t)(uintptr_t)R; R->support = f->b; }
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
        if (f->i < R->plans.n) { f->ph = 4; push(o, fr(OF_SETOP, SO_UNION, f->acc2, plan_work(*(PlanId *)paged_at(&R->plans, f->i)), 0)); return; }
        if (f->i - R->plans.n < R->conns.n) { f->ph = 4; push(o, fr(OF_SETOP, SO_UNION, f->acc2, rec_w(*(ConnectorId *)paged_at(&R->conns, f->i - R->plans.n), 6), 0)); return; }
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
        f->acc = R->plans.n; f->acc2 = R->conns.n;   /* rollback marks */
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
    case 4: if (!o->ret) { paged_truncate(&R->plans, f->acc); paged_truncate(&R->conns, f->acc2); fin(o, 0); return; } f->acc4 = rec_w(rec_w(e, 4), 7); f->i = 0; f->ph = 10; return;
    case 10: {   /* every atom of list acc4 must be available */
        const uint64_t *l; size_t n = list_get(f->acc4, &l);
        if (f->i >= n) { if (expr_tag(e) == EX_PLAN) *(PlanId *)paged_push(&R->plans) = rec_w(e, 2); else *(ConnectorId *)paged_push(&R->conns) = rec_w(e, 4); charge(FR_ALLOCATE_CHUNK); fin(o, 1); return; }
        uint64_t k[4] = { K_MARK, o->id, 5, l[f->i] }; f->ph = 11; push_lookup(o, k, 4); return;
    }
    case 11: if (!o->ret) { paged_truncate(&R->plans, f->acc); paged_truncate(&R->conns, f->acc2); fin(o, 0); return; } xc_add(&W.LX.memo_hit, 1); f->i++; f->ph = 10; return;
    }
}
RealizationId realize(ProblemId p, SetId support, const char **why) { LOCK; RealizationId r = run_op(OF_REALIZE, PH_COMMIT, fr(OF_REALIZE, p, support, 0, 0), why); UNLOCK; return r; }
OpId op_realize(ProblemId p, SetId support) { LOCK; OpId h = op_new(OF_REALIZE, PH_COMMIT, fr(OF_REALIZE, p, support, 0, 0)); UNLOCK; return h; }
static Real *RL(RealizationId r) { require(rec_kind(r) == K_REAL, "not a realization"); return (Real *)side(r)->ptr; }
size_t realization_plans(RealizationId r, const PlanId **out) {
    Real *R = RL(r);
    if (!R->plview && R->plans.n) { R->plview = own(malloc(R->plans.n * sizeof(PlanId))); require(R->plview, "out of memory"); for (size_t i = 0; i < R->plans.n; i++) R->plview[i] = *(PlanId *)paged_at(&R->plans, i); }
    *out = R->plview; return R->plans.n;
}
size_t realization_connectors(RealizationId r, const ConnectorId **out) {
    Real *R = RL(r);
    if (!R->cview && R->conns.n) { R->cview = own(malloc(R->conns.n * sizeof(ConnectorId))); require(R->cview, "out of memory"); for (size_t i = 0; i < R->conns.n; i++) R->cview[i] = *(ConnectorId *)paged_at(&R->conns, i); }
    *out = R->cview; return R->conns.n;
}
SetId realization_work(RealizationId r) { return RL(r)->work; }
Cost realization_cost(RealizationId r) { return RL(r)->cost; }
RefId realization_reference(RealizationId r, RefId *evidence) { Real *R = RL(r); require(R->plans.n, "realization without a plan"); PlanId p0 = *(PlanId *)paged_at(&R->plans, 0); if (evidence) *evidence = plan_evidence(p0); return plan_reference(p0); }

/* ---------------------------------------------------------------- 7. proofs, certificates, the direct fragment, schemas (§69–§70) ---- */

/* proof records: [K_PROOF, rule, F, aux, c1, c2, value]; aux = atom (SPLIT), set (MANDATORY, FACTOR), list [F,G] (DISJOINT_AND, OR_BOUND), list [G, rule] (EQUAL) */
static ProofId proof_intern(ProofRule rule, FormulaId f, uint64_t aux, ProofId c1, ProofId c2, Cost value) { uint64_t w[7] = { K_PROOF, rule, f, aux, c1, c2, value }; return intern_sync(w, 7, NULL); }
static FormulaId mkf_locked(uint64_t tag, FormulaId l, FormulaId r) { return run_op(OF_MKF, W.phase, fr_mkf(tag, l, r), NULL); }
static Cost sum_locked(SetId s, ModelId m, bool *ov) { Op *o = job_sync(fr(OF_SUM, s, m, 0, 0)); uint64_t r = run_locked(o, NULL); if (ov) *ov = o->st == OP_RESOURCE_LIMIT; return r; }
static Cost cmin(Cost a, Cost b) { xc_add(&W.LX.limb_ops, 1); return cost_cmp(a, b) < 0 ? a : b; }
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
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { xc_add(&W.LX.word_compares, 1); if (a[i] == b[j]) { *X = a[i]; *Y = a[1 - i]; *Z = b[1 - j]; return true; } }
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
    case 44: f->acc2 = o->ret; f->ph = 45; push_weight_lookup(o, model, aux); return;   /* the split atom's weight by the framed LOOKUP (§94) */
    case 45: { Cost wc; if (!cost_op(o, f, CA_ADD, weight_from(o->ret, model, aux), f->acc2, 46, &wc)) return; o->ret = wc; }
    /* fall through */
    case 46: { charge(FR_COST_COMPARE_CHUNK); Cost v; if (!cost_op(o, f, CA_MIN, f->acc, o->ret, 47, &v)) return; o->ret = v; }
    /* fall through */
    case 47: { Cost v = o->ret; if (v != value) { fail(o, "SPLIT value is not the minimum of its branches"); return; } proof_done(o, f, v); return; }
    /* FACTOR */
    case 51: if (o->ret != aux) { fail(o, "FACTOR set is not Must(F)"); return; } f->ph = 52; push(o, fr(OF_SUBST, F, aux, 1, 0)); return;
    case 52: if (!c1 || o->ret != proof_formula(c1)) { fail(o, "FACTOR child does not concern F[M := 1]"); return; } f->ph = 53; push(o, fr(OF_PROOF, c1, model, 0, 0)); return;
    case 53: f->acc = o->ret; f->ph = 54; push(o, fr(OF_SUM, aux, model, 0, 0)); return;
    case 54: { Cost v; if (!cost_op(o, f, CA_ADD, o->ret, f->acc, 55, &v)) return; o->ret = v; }
    /* fall through */
    case 55: { Cost v = o->ret; if (v != value) { fail(o, "FACTOR value is not weight(M) + residual bound"); return; } proof_done(o, f, v); return; }
    /* DISJOINT_AND */
    case 61: { const uint64_t *l; list_get(aux, &l); if (o->ret != F) { fail(o, "DISJOINT_AND node formula is not the conjunction of its parts"); return; } if (!c1 || !c2 || proof_formula(c1) != l[0] || proof_formula(c2) != l[1]) { fail(o, "DISJOINT_AND children prove other formulas"); return; } f->ph = 62; push(o, fr(OF_SUPPORT, l[0], 0, 0, 0)); return; }
    case 62: { const uint64_t *l; list_get(aux, &l); f->acc = o->ret; f->ph = 63; push(o, fr(OF_SUPPORT, l[1], 0, 0, 0)); return; }
    case 63: f->ph = 64; push(o, fr(OF_SETOP, SO_INTER, f->acc, o->ret, 0)); return;
    case 64: if (o->ret != W.EMPTY) { fail(o, "DISJOINT_AND: supports are not disjoint"); return; } f->ph = 65; push(o, fr(OF_PROOF, c1, model, 0, 0)); return;
    case 65: f->acc = o->ret; f->ph = 66; push(o, fr(OF_PROOF, c2, model, 0, 0)); return;
    case 66: { Cost v; if (!cost_op(o, f, CA_ADD, f->acc, o->ret, 67, &v)) return; o->ret = v; }
    /* fall through */
    case 67: { Cost v = o->ret; if (v != value) { fail(o, "DISJOINT_AND value is not the sum of its parts"); return; } proof_done(o, f, v); return; }
    /* OR_BOUND */
    case 71: { const uint64_t *l; list_get(aux, &l); if (o->ret != F) { fail(o, "OR_BOUND node formula is not the disjunction of its parts"); return; } if (!c1 || !c2 || proof_formula(c1) != l[0] || proof_formula(c2) != l[1]) { fail(o, "OR_BOUND children prove other formulas"); return; } f->ph = 72; push(o, fr(OF_PROOF, c1, model, 0, 0)); return; }
    case 72: f->acc = o->ret; f->ph = 73; push(o, fr(OF_PROOF, c2, model, 0, 0)); return;
    case 73: { charge(FR_COST_COMPARE_CHUNK); Cost v; if (!cost_op(o, f, CA_MIN, f->acc, o->ret, 74, &v)) return; o->ret = v; }
    /* fall through */
    case 74: { Cost v = o->ret; if (v != value) { fail(o, "OR_BOUND value is not the minimum of its parts"); return; } proof_done(o, f, v); return; }
    /* WEAKEN */
    case 81: { charge(FR_COST_COMPARE_CHUNK); Cost c; if (!cost_op(o, f, CA_CMP, value, o->ret, 82, &c)) return; o->ret = c; }
    /* fall through */
    case 82: { if (o->ret == 2) { fail(o, "WEAKEN claims more than its child"); return; } proof_done(o, f, value); return; }   /* CA_CMP: 0 less, 1 equal, 2 greater */
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
        charge(FR_COST_COMPARE_CHUNK); xc_add(&W.LX.limb_ops, 1);
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
        if (!side(id)->ptr) { RedRec *rr = pool_take(sizeof *rr); rr->r.formula = F; rr->r.reduced = (f->e & 1) != 0; rr->r.value = f->acc; rr->r.lower = f->acc3; rr->r.attaining = f->acc2; side(id)->ptr = rr; }
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
        charge(FR_COST_COMPARE_CHUNK); f->acc2 = o->ret;
        Cost c; if (!cost_op(o, f, CA_CMP, l->value, rg->value, 12, &c)) return; o->ret = c;
    }
    /* fall through */
    case 12: {
        Reduction *l = RED(f->acc), *rg = RED(f->acc2); bool left = o->ret <= 1;
        reduce_finish(o, f, true, left ? l->value : rg->value, left ? l->attaining : rg->attaining, PR_OR_BOUND, true, formula_left(F), formula_right(F), l->lower, rg->lower); return;
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
        f->acc4 = o->ret;
        Cost v; if (!cost_op(o, f, CA_ADD, l->value, rg->value, 26, &v)) return; o->ret = v;
    }
    /* fall through */
    case 26: {
        Reduction *l = RED(f->acc3), *rg = RED(f->acc4); Cost v = o->ret; f->acc = v;
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
        Reduction *g0 = RED(f->acc3); Cost v0; if (!cost_op(o, f, CA_ADD, o->ret, g0->value, 35, &v0)) return; o->ret = v0;
    }
    /* fall through */
    case 35: {
        Reduction *g = RED(f->acc3); Cost v = o->ret;
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
/* MAPF: a = F, b = map; memo (F, map) */
static void step_mapf(Op *o, Frame *f) {
    FormulaId F = f->a;
    switch (f->ph) {
    case 0: {
        FormulaTag t = formula_tag(F);
        if (t == FM_ZERO || t == FM_ONE) { fin(o, F); return; }
        if (t == FM_ATOM) { f->ph = 7; push_amap_lookup(o, f->b, formula_atom_of(F)); return; }
        uint64_t k[4] = { K_MEMO, 0xA1, F, f->b }; f->ph = 1; push_lookup(o, k, 4); return;
    }
    case 1:
        if (o->ret && side(o->ret)->has_val) { xc_add(&W.LX.memo_hit, 1); xc_add(&W.LX.memo_deliver, 1); fin(o, side(o->ret)->val); return; }
        f->ph = 2; push(o, fr(OF_MAPF, formula_left(F), f->b, 0, 0)); return;
    case 2: f->acc = o->ret; f->ph = 3; push(o, fr(OF_MAPF, formula_right(F), f->b, 0, 0)); return;
    case 3: f->ph = 4; push(o, fr_mkf(formula_tag(F), f->acc, o->ret)); return;
    case 4: { f->acc3 = o->ret; uint64_t k[4] = { K_MEMO, 0xA1, F, f->b }; f->ph = 6; push_intern(o, k, 4); return; }
    case 5: fin(o, o->ret); return;
    case 6: { Side *s = side(o->ret); s->val = f->acc3; s->has_val = true; fin(o, f->acc3); return; }
    case 7: f->ph = 5; push(o, fr_mkf(FM_ATOM, amap_from(o->ret, formula_atom_of(F)), 0)); return;   /* the atom's image by the framed LOOKUP (§94) */
    }
}
/* MAPSET: a = set, b = map: direct image */
static void step_mapset(Op *o, Frame *f) {
    size_t n; const AtomId *S = set_atoms(f->a, &n);
    switch (f->ph) {
    case 0: if (f->i < n) { f->ph = 2; push_amap_lookup(o, f->b, S[f->i]); return; } f->ph = 1; push(o, fr_sort_own(K_SET, &f->buf)); return;
    case 2: pw_push(&f->buf, amap_from(o->ret, S[f->i])); f->i++; f->ph = 0; return;   /* one image per framed LOOKUP (§94) */
    case 1: fin(o, o->ret); return;
    }
}
/* MAPP: a = proof, b = map, c = model: rebuild the proof node over the mapped formulas/sets with recomputed values */
/* R6: the mapped proof's records (aux list, proof) are interned by framed
 * children; the finishing data lives in the frame as for REDUCE (acc3 = rule
 * → proof, acc4 = mapped formula, i/j = aux words, buf3 = child proofs) */
static void mapp_finish(Op *o, Frame *f, ProofRule rule, FormulaId formula, bool aux_list, uint64_t aux0, uint64_t aux1, ProofId c1, ProofId c2, Cost value) {
    (void)o; f->acc3 = rule; f->acc4 = formula; f->i = aux0; f->j = aux1; f->acc = value; f->e = aux_list ? 2u : 0u;
    paged_truncate(&f->buf3, 0); pw_push(&f->buf3, c1); pw_push(&f->buf3, c2);
    f->ph = 90;
}
static void step_mapp(Op *o, Frame *f) {
    size_t n; const uint64_t *w = rec_words(f->a, &n); ProofRule rule = (ProofRule)w[1]; uint64_t aux = w[3]; ProofId c1 = w[4], c2 = w[5];
    switch (f->ph) {
    case 90: if (f->e & 2) { uint64_t lw[3] = { K_LIST, f->i, f->j }; f->ph = 91; push_intern(o, lw, 3); return; } f->ph = 92; return;
    case 91: f->i = o->ret; f->ph = 92; return;
    case 92: { uint64_t pw[7] = { K_PROOF, f->acc3, f->acc4, f->i, pw_get(&f->buf3, 0), pw_get(&f->buf3, 1), f->acc }; f->ph = 93; push_intern(o, pw, 7); return; }
    case 93: fin(o, o->ret); return;
    case 0: f->ph = 1; push(o, fr(OF_MAPF, w[2], f->b, 0, 0)); return;
    case 1:
        f->acc = o->ret;   /* mapped F */
        switch (rule) {
        case PR_TRIVIAL: mapp_finish(o, f, PR_TRIVIAL, f->acc, false, 0, 0, 0, 0, 0); return;
        case PR_FALSE: mapp_finish(o, f, PR_FALSE, W.ZERO, false, 0, 0, 0, 0, COST_INF); return;
        case PR_MANDATORY: case PR_FACTOR: f->ph = 2; push(o, fr(OF_MAPSET, aux, f->b, 0, 0)); return;
        case PR_SPLIT: f->ph = 16; push_amap_lookup(o, f->b, aux); return;
        case PR_DISJOINT_AND: case PR_OR_BOUND: { const uint64_t *l; list_get(aux, &l); f->ph = 6; push(o, fr(OF_MAPF, l[0], f->b, 0, 0)); return; }
        case PR_WEAKEN: f->ph = 10; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
        case PR_EQUAL: { const uint64_t *l; list_get(aux, &l); f->ph = 11; push(o, fr(OF_MAPF, l[0], f->b, 0, 0)); return; }
        default: fail(o, "unknown proof rule"); return;
        }
    case 2: f->acc2 = o->ret; f->ph = rule == PR_MANDATORY ? 13 : 3; push(o, fr(OF_SUM, f->acc2, f->c, 0, 0)); return;
    case 13: mapp_finish(o, f, PR_MANDATORY, f->acc, false, f->acc2, 0, 0, 0, o->ret); return;
    case 3: f->acc3 = o->ret; f->ph = 14; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
    case 14: { f->acc4 = o->ret; Cost v; if (!cost_op(o, f, CA_ADD, f->acc3, rec_w(o->ret, 6), 18, &v)) return; o->ret = v; }
    /* fall through */
    case 18: mapp_finish(o, f, PR_FACTOR, f->acc, false, f->acc2, 0, f->acc4, 0, o->ret); return;
    case 4: f->acc3 = o->ret; f->ph = 5; push(o, fr(OF_MAPP, c2, f->b, f->c, 0)); return;
    case 16: f->acc2 = amap_from(o->ret, aux); f->ph = 4; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;   /* the split atom's image by the framed LOOKUP (§94) */
    case 5: f->d = o->ret; f->ph = 17; push_weight_lookup(o, f->c, f->acc2); return;                   /* its weight by the framed LOOKUP (§94) */
    case 17: { Cost wc; if (!cost_op(o, f, CA_ADD, weight_from(o->ret, f->c, f->acc2), rec_w(f->d, 6), 19, &wc)) return; o->ret = wc; }
    /* fall through */
    case 19: { Cost v; if (!cost_op(o, f, CA_MIN, rec_w(f->acc3, 6), o->ret, 20, &v)) return; o->ret = v; }
    /* fall through */
    case 20: mapp_finish(o, f, PR_SPLIT, f->acc, false, f->acc2, 0, f->acc3, f->d, o->ret); return;
    case 6: { const uint64_t *l; list_get(aux, &l); f->acc2 = o->ret; f->ph = 7; push(o, fr(OF_MAPF, l[1], f->b, 0, 0)); return; }
    case 7: f->acc3 = o->ret; f->ph = 8; push(o, fr(OF_MAPP, c1, f->b, f->c, 0)); return;
    case 8: f->acc4 = o->ret; f->ph = 9; push(o, fr(OF_MAPP, c2, f->b, f->c, 0)); return;
    case 9: {   /* the mapped formula by the framed MKF, then the framed finish */
        f->acc = o->ret;   /* second mapped child proof (the mapped F in acc is no longer needed) */
        f->ph = 15; push(o, fr_mkf(rule == PR_DISJOINT_AND ? FM_AND : FM_OR, f->acc2, f->acc3)); return;
    }
    case 15: { f->i = o->ret;   /* the mapped formula */
        Cost v; if (!cost_op(o, f, rule == PR_DISJOINT_AND ? CA_ADD : CA_MIN, rec_w(f->acc4, 6), rec_w(f->acc, 6), 21, &v)) return; o->ret = v; }
    /* fall through */
    case 21: mapp_finish(o, f, rule, f->i, true, f->acc2, f->acc3, f->acc4, f->acc, o->ret); return;
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
    Geo *x = pool_take(sizeof *x); x->n = nstates;
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
        f->j = f->i - 1;   /* the edge under examination */
        Cost rhs; if (!cost_op(o, f, CA_ADD, e.c, x->V[e.to], 2, &rhs)) return; o->ret = rhs;
    }
    /* fall through */
    case 2: { GEdge e = x->edges.data[f->j]; charge(FR_COST_COMPARE_CHUNK); Cost c; if (!cost_op(o, f, CA_CMP, x->V[e.from], o->ret, 3, &c)) return; o->ret = c; }
    /* fall through */
    case 3: if (o->ret == 2) { fail(o, "lower-bound inequality V(s) <= c + V(s') fails on an admitted edge"); return; } f->ph = 0; return;
    case 1: {
        if (f->i >= x->n) { fin(o, x->V[f->b]); return; }
        uint64_t s = f->i++;
        if (x->terminal[s]) { if (x->V[s] != 0) { fail(o, "a successful terminal must have V = 0"); return; } return; }
        if (x->V[s] == COST_INF) return;   /* outside the attaining policy's domain */
        if (!x->policy[s]) { fail(o, "no attaining step at a nonterminal state of the domain"); return; }
        GEdge e = x->edges.data[x->policy[s] - 1];
        if (e.from != s) { fail(o, "selected step does not start at its state"); return; }
        f->j = s; charge(FR_COST_COMPARE_CHUNK);
        Cost rhs; if (!cost_op(o, f, CA_ADD, e.c, x->V[e.to], 4, &rhs)) return; o->ret = rhs;
    }
    /* fall through */
    case 4: {
        uint64_t s = f->j; GEdge e = x->edges.data[x->policy[s] - 1];
        f->ph = 1;
        if (x->V[s] != o->ret) { fail(o, "selected step does not attain V(s) = c + V(s')"); return; }
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
/* EFFECT-AUTHORITY §3: the framed proof-use audit of (Γ, φ, e, E) as a public
 * operation (admission, context, formation, e : E as kernel continuations,
 * then the dependency audit), stepped by op_step like every operation */
OpId op_proof_audit(ContextId G, FaceId phi, RefId e, RefId E) { LOCK; OpId h = op_new(OF_AUDIT, PH_CHECK, fr(OF_AUDIT, G, phi, e, E)); UNLOCK; return h; }
int op_audit_verdict(OpId h, size_t *nassume, const uint64_t **assume) {
    int r; LOCK; Op *o = JOB(HND(h)->job);
    if (o->st == OP_RUNNING) r = -1;
    else if (o->st == OP_INVALID) r = o->unresolved ? PU_UNRESOLVED : PU_INVALID;
    else {
        r = (int)rec_w(o->result, 1);
        if (nassume) { size_t n = 0; const AtomId *a = rec_w(o->result, 2) ? set_atoms(rec_w(o->result, 2), &n) : NULL; *nassume = n; if (assume) *assume = a; }
    }
    UNLOCK; return r;
}
OpId op_geo_check(GeoId g, uint64_t root) { LOCK; OpId h = op_new(OF_GEO, PH_CHECK, fr(OF_GEO, g, root, 0, 0)); UNLOCK; return h; }

/* ---------------------------------------------------------------- 9. ledger, lifecycle ---- */
static const char *fam_names[FR_COUNT] = { "PREPARE_VISIT", "VALIDATE_PREPARED_BOUNDARY", "FORMULA_VISIT", "FORMULA_INTERN_STEP", "COFACTOR_VISIT", "COFACTOR_REBUILD", "SUPPORT_CHUNK", "MUST_CHUNK", "COST_ADD_CHUNK", "COST_COMPARE_CHUNK", "CERTIFICATE_VISIT", "REALIZATION_VISIT", "ALLOCATE_CHUNK", "RELEASE_CHUNK", "TABLE_PROBE", "DEMAND_VISIT", "SPECIALIZE_VISIT", "FAMILY_CHUNK", "GEODESIC_VISIT", "PRODUCER_LOOKUP", "ALIAS_DELIVERY", "SHAPE_NODE", "DEPENDENCY_CHECK", "RECEIPT", "PROOF_USE_AUDIT", "SCHEDULE_STEP", "CYCLE_CHECK", "KERNEL_TRANSITION" };
const char *frame_family_name(FrameFamily f) { return fam_names[f]; }
#define XP(x) xs_u64_checked(xc_snap(&(x)), "work ledger")
WorkLedger work_ledger(void) {
    LOCK; WorkLedger l = W.L;
    for (int i = 0; i < FR_COUNT; i++) l.frames[i] = XP(W.LX.frames[i]);
    for (int i = 0; i < PH_COUNT; i++) l.by_phase[i] = XP(W.LX.by_phase[i]);
    l.probes = XP(W.LX.probes); l.word_compares = XP(W.LX.word_compares); l.limb_ops = XP(W.LX.limb_ops); l.alloc_words = XP(W.LX.alloc_words); l.release_words = XP(W.LX.release_words);
    l.memo_lookup = XP(W.LX.memo_lookup); l.memo_hit = XP(W.LX.memo_hit); l.memo_deliver = XP(W.LX.memo_deliver); l.kernel_calls = XP(W.LX.kernel_calls);
    ledger_fold_late(&l); UNLOCK; return l;
}
WorkLedgerExact work_ledger_exact(void) {
    WorkLedgerExact x; LOCK;
    for (int i = 0; i < FR_COUNT; i++) x.frames[i] = xc_snap(&W.LX.frames[i]);
    for (int i = 0; i < PH_COUNT; i++) x.by_phase[i] = xc_snap(&W.LX.by_phase[i]);
    x.probes = xc_snap(&W.LX.probes); x.word_compares = xc_snap(&W.LX.word_compares); x.limb_ops = xc_snap(&W.LX.limb_ops); x.alloc_words = xc_snap(&W.LX.alloc_words); x.release_words = xc_snap(&W.LX.release_words);
    x.memo_lookup = xc_snap(&W.LX.memo_lookup); x.memo_hit = xc_snap(&W.LX.memo_hit); x.memo_deliver = xc_snap(&W.LX.memo_deliver); x.kernel_calls = xc_snap(&W.LX.kernel_calls);
    UNLOCK; return x;
}
static void ledger_zero(void) {
    memset(&W.L, 0, sizeof W.L);
    for (int i = 0; i < FR_COUNT; i++) xc_reset(&W.LX.frames[i]);
    for (int i = 0; i < PH_COUNT; i++) xc_reset(&W.LX.by_phase[i]);
    xc_reset(&W.LX.probes); xc_reset(&W.LX.word_compares); xc_reset(&W.LX.limb_ops); xc_reset(&W.LX.alloc_words); xc_reset(&W.LX.release_words);
    xc_reset(&W.LX.memo_lookup); xc_reset(&W.LX.memo_hit); xc_reset(&W.LX.memo_deliver); xc_reset(&W.LX.kernel_calls);
}
void work_ledger_reset(void) {
    LOCK; ledger_zero();
    { static const ReuseCounter rc_of[3] = { REUSE_SHAPE_NODE, REUSE_DEPENDENCY_CHECK, REUSE_RECEIPT_INSTANCE };
      for (int ph = 0; ph < PH_COUNT; ph++) for (int k = 0; k < 3; k++) W.late_base[ph][k] = reuse_scope_late_snap(ph, rc_of[k]); }
    UNLOCK;
}
void work_set_phase(Phase p) { LOCK; W.phase = p; UNLOCK; }
Phase work_phase(void) { return W.phase; }
uint64_t work_total_frames(void) { WorkLedger l = work_ledger(); uint64_t t = 0; for (int i = 0; i < FR_COUNT; i++) { require(t <= UINT64_MAX - l.frames[i], "work_total_frames: outside a machine word"); t += l.frames[i]; } return t; }
void work_record_execution(EvalEvents b, EvalNetEvents nb, EvalEvents a, EvalNetEvents na) {
    LOCK;
    W.L.exec_eval.request += a.request - b.request; W.L.exec_eval.eval_step += a.eval_step - b.eval_step; W.L.exec_eval.publish += a.publish - b.publish; W.L.exec_eval.deliver += a.deliver - b.deliver;
    W.L.exec_eval.ready_hit += a.ready_hit - b.ready_hit; W.L.exec_eval.running_hit += a.running_hit - b.running_hit; W.L.exec_eval.launch += a.launch - b.launch;
    W.L.exec_net.apply += na.apply - nb.apply; W.L.exec_net.continue_ref += na.continue_ref - nb.continue_ref; W.L.exec_net.op += na.op - nb.op; W.L.exec_net.eval_deliver += na.eval_deliver - nb.eval_deliver; W.L.exec_net.retries += na.retries - nb.retries;
    xc_add(&W.LX.by_phase[PH_EXECUTE], (a.eval_step - b.eval_step) + (na.op - nb.op) + (na.apply - nb.apply) + (na.continue_ref - nb.continue_ref));
    UNLOCK;
}

void work_init(void) {
    memset(&W, 0, sizeof W);
    { static const ReuseCounter rc_of[3] = { REUSE_SHAPE_NODE, REUSE_DEPENDENCY_CHECK, REUSE_RECEIPT_INSTANCE };
      for (int ph = 0; ph < PH_COUNT; ph++) for (int k = 0; k < 3; k++) W.late_base[ph][k] = reuse_scope_late_snap(ph, rc_of[k]); }
    pthread_mutex_init(&W.mu, NULL);
    arena_init(); paged_init(&W.owned, sizeof(void *)); paged_init(&W.dead, sizeof(Paged));
    spare_init(&W.spare[0], CHUNK_SIZE * sizeof(Side)); spare_init(&W.spare[1], CHUNK_SIZE * sizeof(Handle)); spare_init(&W.spare[2], CHUNK_SIZE * sizeof(size_t));
    ktab_init(&W.tab); chunked_init(&W.side, sizeof(Side)); chunked_init(&W.ops, sizeof(Handle));
    chunked_set_alloc(&W.side, chunk_from_spare, &W.spare[0]); chunked_set_alloc(&W.ops, chunk_from_spare, &W.spare[1]); chunked_set_alloc(&W.tab.off, chunk_from_spare, &W.spare[2]);
    uint64_t z[4] = { K_FORMULA, FM_ZERO, 0, 0 }, one[4] = { K_FORMULA, FM_ONE, 0, 0 }, e[1] = { K_SET };
    W.ZERO = intern_sync(z, 4, NULL); W.ONE = intern_sync(one, 4, NULL); W.EMPTY = intern_sync(e, 1, NULL);
    uint64_t f0[1] = { K_FAMILY }, f1[2] = { K_FAMILY, W.EMPTY };
    W.FAM0 = intern_sync(f0, 1, NULL); W.FAM1 = intern_sync(f1, 2, NULL);
    ledger_zero();
    W.live = true; kc_session(KC_MOD_WORK, true);
}
void work_free(void) {
    if (!W.live) return;
    /* V23 R3: under the closed-session precondition every kernel continuation
     * still attached to a frame is destroyed, not evaluated: a completed one
     * is freed; a started, uncompleted one — a finite call that has not
     * finished, a pending wait, a member of a waiting cycle — is cancelled:
     * its thread runs its registered releases and unwinds through its stack
     * segments to its base, its allocation registry is reaped after the
     * machine's structures, and the record is freed (kc_cancel). Each
     * continuation's accounting scope is closed and released exactly once;
     * the events it executed stay counted. No result is published. */
    {
        Words ks; words_init(&ks);
        for (size_t i = 1; i <= W.tab.n; i++) {
            Side *sd = side(i); if (!sd->ptr || sd->kind != K_JOB) continue; Op *o = sd->ptr;
            for (size_t k = 0; k < o->stack.n; k++) { Frame *f = paged_at(&o->stack, k); if (f->fam == OF_KERNEL && f->ph == 1 && f->acc) { words_push(&ks, f->acc); f->acc = 0; } }
        }
        for (size_t i = 0; i < ks.n; i++) {
            KCont *k = (KCont *)(uintptr_t)ks.w[i]; if (!k) continue;
            ReuseScope *acct = k->acct;
            kc_cancel(k);                                 /* frees a completed or never-started record directly */
            if (acct) { reuse_scope_close(acct); reuse_scope_unref(acct); }
        }
        W.kc_active = NULL; W.kc_owner = 0;
        words_free(&ks);
    }
    kc_shutdown();
    for (size_t i = 1; i <= W.tab.n; i++) {
        Side *s = side(i); if (!s->ptr) continue;
        switch (s->kind) {
        case K_JOB: { Op *o = s->ptr; for (size_t k = 0; k < o->stack.n; k++) { Frame *f = paged_at(&o->stack, k); paged_retire(&f->buf); paged_retire(&f->buf2); paged_retire(&f->buf3); } paged_retire(&o->stack); paged_retire(&o->waiters); paged_retire(&o->path); break; }
        case K_DGRAPH: { DGraph *d = s->ptr; for (size_t k = 0; k < d->nodes.len; k++) { vec_free(&d->nodes.data[k].occ); vec_free(&d->nodes.data[k].applies); } vec_free(&d->nodes); vec_free(&d->roots); vec_free(&d->applies); break; }
        case K_DEMAND: { Demand *d = s->ptr; paged_retire(&d->producers); paged_retire(&d->occ); break; }
        case K_REAL: { Real *r = s->ptr; paged_retire(&r->plans); paged_retire(&r->conns); break; }
        case K_GEO: { Geo *g = s->ptr; vec_free(&g->edges); break; }
        default: break;
        }
    }
    while (W.dead.n) dead_stack_step();   /* teardown: the remaining dead frames */
    paged_retire(&W.dead);
    for (size_t i = 0; i < W.owned.n; i++) free(*(void **)paged_at(&W.owned, i));
    paged_retire(&W.owned);
    ktab_free(&W.tab); chunked_free(&W.side); chunked_free(&W.ops);
    for (int i = 0; i < 16; i++) if (W.pool_sizes[i]) paged_retire(&W.pool[i]);
    for (int i = 0; i < 3; i++) if (W.spare[i].block) arena_release(W.spare[i].block, W.spare[i].words);
    arena_reap_all(); arena_free();
    pthread_mutex_destroy(&W.mu);
    W.live = false; kc_session(KC_MOD_WORK, false);
}

/* white-box probes that include this file stage frame buffers with
 * `words_push`; the frame buffers are paged (§94), so the name dispatches on
 * the buffer type for them */
static inline void words_push_words(Words *b, uint64_t x) { words_push(b, x); }
#define words_push(b, x) _Generic((b), Paged *: pw_push, Words *: words_push_words)((b), (x))
