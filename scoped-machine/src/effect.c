/* effect.c — witnessed effects, authority and ports (effect.h). */
#include "effect.h"
#include "judge.h"
#include "check.h"
#include "proof.h"
#include "chain.h"
#include "lib.h"

enum { T_SCHEMA = 0xEF01, T_AUTH, T_HEAD, T_PORT, T_CAP, T_PROP, T_OCC, T_PREP, T_OUT, T_VIEW };
enum { CK_HEAD = 1, CK_PORT };

/* ---------------- cells and descriptors ---------------- */
typedef struct Desc Desc;
typedef struct { Desc *D; size_t k; } Node;
enum { D_RESERVING = 0, D_COMMITTED, D_ABORTED };
struct Desc {
    int state;                          /* the one acceptance point: RESERVING → COMMITTED | ABORTED */
    uint64_t rid, prop, occ;
    size_t n;                           /* inputs, in reservation order */
    size_t nt;                          /* inputs, then output port cells (expect absent, after the port) */
    size_t base;                        /* its cells: EF.dcells[base .. base + nt) */
};
/* a descriptor's cell k: the cell, what it expects, what it becomes, and the node a reservation names */
typedef struct { uint64_t cell, ckey, expect, after; Node node; } DCell;
/* a cell word: 0 absent | AVAILABLE(x) | RESERVED(node) | CONSUMED(occurrence) */
#define W_AVAIL(x) (((uint64_t)(x) << 2) | 1)
#define W_CONS(o) (((uint64_t)(o) << 2) | 3)
#define W_RES(nd) ((uint64_t)(uintptr_t)(nd) | 2)
#define W_TAG(w) ((w) & 3)
#define W_VAL(w) ((w) >> 2)
#define W_NODE(w) ((Node *)(uintptr_t)((w) & ~(uint64_t)3))

static struct {
    KeyedSlots cells;                   /* [kind, id] → its word */
    KeyedSlots rids;                    /* request id → [proposal, settled outcome] */
    Interner issued;                    /* capabilities an authority issued */
    KeyedSlots occs;                    /* occurrence → its descriptor */
    Chunked descs, dcells;              /* descriptors and their cells, in fixed-size chunks */
    size_t ndescs, ndcells;
} EF;
static DCell *DC(const Desc *D, size_t k) { return chunked_at(&EF.dcells, D->base + k); }

static uint64_t *cell_word(uint64_t kind, uint64_t id) { uint64_t w[2] = { kind, id }; return keyed_slot(&EF.cells, w, 2, NULL); }
/* the logical value of a cell: a reservation read through its descriptor */
static uint64_t logical(uint64_t w) {
    if (W_TAG(w) != 2) return w;
    Node *nd = W_NODE(w);
    int s = __atomic_load_n(&nd->D->state, __ATOMIC_ACQUIRE);
    return s == D_COMMITTED ? DC(nd->D, nd->k)->after : DC(nd->D, nd->k)->expect;
}
static uint64_t cell_logical(uint64_t kind, uint64_t id) { return logical(__atomic_load_n(cell_word(kind, id), __ATOMIC_ACQUIRE)); }

/* ---------------- records ---------------- */
uint64_t effect_schema(RefId S, uint64_t level, RefId R) { return RQ(T_SCHEMA, S, level, R); }
uint64_t effect_authority(uint64_t schema, RefId s0, uint64_t nonce, uint64_t *cap) {
    uint64_t a = RQ(T_AUTH, schema, nonce), h = RQ(T_HEAD, a, 0, s0, 0);
    uint64_t expected = 0;
    __atomic_compare_exchange_n(cell_word(CK_HEAD, a), &expected, W_AVAIL(h), false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
    uint64_t c = RQ(T_CAP, a, nonce);
    interner_intern(&EF.issued, &c, 1, NULL);
    if (cap) *cap = c;
    return a;
}
uint64_t effect_capability_unissued(uint64_t authority, uint64_t nonce) { return RQ(T_CAP, authority, nonce | (1ULL << 62)); }
static RefId value_of(uint64_t rec) {             /* a head's state or a port's payload */
    size_t n; const uint64_t *w = rget(rec, &n);
    return w[0] == T_HEAD ? w[3] : w[3];
}
static uint64_t cell_kind_of(uint64_t rec) { return rword(rec, 0) == T_HEAD ? CK_HEAD : CK_PORT; }
static uint64_t cell_id_of(uint64_t rec) { size_t n; const uint64_t *w = rget(rec, &n); return w[0] == T_HEAD ? w[1] : rec; }
uint64_t effect_proposal(uint64_t schema, size_t nin, const uint64_t *inputs, size_t nout, const EffOut *outs, RefId witness, size_t ncap, const uint64_t *caps) {
    size_t ns; const uint64_t *sc = rget(schema, &ns);
    RefId T = sc[3];
    for (size_t i = 0; i < nin; i++) T = mk_app(T, value_of(inputs[i]));
    for (size_t i = 0; i < nout; i++) T = mk_app(T, outs[i].value);
    size_t n = 3 + nin + 1 + 3 * nout + 3 + ncap + nin;
    uint64_t *w = malloc(n * sizeof *w); require(w, "out of memory: a proposal");
    size_t q = 0;
    w[q++] = T_PROP; w[q++] = schema; w[q++] = nin;
    for (size_t i = 0; i < nin; i++) w[q++] = inputs[i];
    w[q++] = nout;
    for (size_t i = 0; i < nout; i++) { w[q++] = (uint64_t)outs[i].is_port; w[q++] = outs[i].authority; w[q++] = outs[i].value; }
    w[q++] = witness; w[q++] = T; w[q++] = ncap;
    for (size_t i = 0; i < ncap; i++) w[q++] = caps[i];
    /* the reservation order: the fixed total order on (cell kind, cell id) */
    for (size_t i = 0; i < nin; i++) w[q + i] = i;
    for (size_t i = 1; i < nin; i++) for (size_t j = i; j > 0; j--) {
        uint64_t a = w[q + j - 1], b = w[q + j];
        uint64_t ka = cell_kind_of(inputs[a]), kb = cell_kind_of(inputs[b]), ia = cell_id_of(inputs[a]), ib = cell_id_of(inputs[b]);
        if (ka > kb || (ka == kb && ia > ib)) { w[q + j - 1] = b; w[q + j] = a; } else break;
    }
    uint64_t p = rq(n, w); free(w); return p;
}
/* proposal accessors */
typedef struct { const uint64_t *w; size_t nin, nout, ncap; const uint64_t *in, *out, *cap, *ord; RefId witness, wtype; uint64_t schema; } Prop;
static Prop prop_of(uint64_t p) {
    Prop P; size_t n; P.w = rget(p, &n);
    P.schema = P.w[1]; P.nin = (size_t)P.w[2]; P.in = P.w + 3;
    P.nout = (size_t)P.w[3 + P.nin]; P.out = P.w + 4 + P.nin;
    const uint64_t *t = P.out + 3 * P.nout;
    P.witness = t[0]; P.wtype = t[1]; P.ncap = (size_t)t[2]; P.cap = t + 3; P.ord = P.cap + P.ncap;
    return P;
}
Outcome outcome_kind(uint64_t out) { return (Outcome)rword(out, 1); }
uint64_t outcome_occurrence(uint64_t out) { size_t n; const uint64_t *w = rget(out, &n); return w[1] == OUT_ACCEPTED ? w[2] : 0; }
const char *outcome_reason(uint64_t out) { size_t n; const uint64_t *w = rget(out, &n); return w[1] == OUT_INVALID ? (const char *)(uintptr_t)w[2] : ""; }


/* ---------------- PREPARE(P) ----------------
 * The mathematical premises are judge.admit requests (check.c), the same
 * judgments the public interface decodes: the state type at its declared
 * level, every state at it, and the witness's proof use at the schema's edge
 * type (typing, the bodies of the revisions read and audited validated, the
 * proof-use classification). Its result retains that proof-use judgment. */
typedef struct { size_t i, j, c, cnt, n; uint64_t t, r, need, issuer, ok, ev, G, fv; Prop p, ip; const char *bad; } PrLoc;
static uint64_t prep_res(int ok, const char *why, uint64_t ev) { return RQ(T_PREP, (uint64_t)ok, (uint64_t)(uintptr_t)why, ev); }
static uint64_t state_at(const Prop *p, size_t i) { return i < p->nin ? value_of(p->in[i]) : p->out[3 * (i - p->nin) + 2]; }
static int admit_code(uint64_t r) { return rword(r, 0) == 1 ? 1 : rword(r, 0) == 3 ? 3 : 2; }
static void prep_step(Cont *k, uint64_t v) {
    PrLoc *L = FR_LOC(k, PrLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->p = prop_of(k->w[0]);
    require(rword(L->p.schema, 0) == T_SCHEMA, "a proposal without a schema");
    /* its typed boundary: the free variables of the schema, the states and
     * the witness, a context in declaration order (one per step) */
    L->fv = ref_freevars(rword(L->p.schema, 1));
    FR_AWAIT(k, L->fv, F_SUNION, L->fv, ref_freevars(rword(L->p.schema, 3)));
    for (L->i = 0; L->i < L->p.nin + L->p.nout; L->i++) FR_AWAIT(k, L->fv, F_SUNION, L->fv, ref_freevars(state_at(&L->p, L->i)));
    FR_AWAIT(k, L->fv, F_SUNION, L->fv, ref_freevars(L->p.witness));
    L->G = jc_empty();
    for (L->i = 0; L->i < (set_get(L->fv, &L->n), L->n); L->i++) { size_t n; FR_AWAIT(k, L->G, J_EXT, L->G, subst_entry(set_get(L->fv, &n)[L->i], S_TERM, 0)); }
    /* the state type at its declared level, exactly */
    {   size_t n; const uint64_t *sc = rget(L->p.schema, &n); L->t = sc[1]; L->r = sc[2]; }
    FR_AWAIT(k, r, J_ADMIT, RQ(AD_ISTYPE, L->G, fc_true(), L->t, 0, 0), 0);
    if (admit_code(r) != 1) FR_FINISH(k, prep_res(admit_code(r), "the state type is not a type", 0));
    if (rword(r, 2) != L->r) FR_FINISH(k, prep_res(2, "the state type is not at its declared level", 0));
    /* every input and output state at the state type */
    for (L->i = 0; L->i < L->p.nin + L->p.nout; L->i++) {
        FR_AWAIT(k, r, J_ADMIT, RQ(AD_CHECK, L->G, fc_true(), state_at(&L->p, L->i), L->t, 0), 0);
        if (admit_code(r) != 1) FR_FINISH(k, prep_res(admit_code(r), "a state is not of the state type", 0));
    }
    /* the witness type is R at the states, built here through the construction family */
    {   L->t = rword(L->p.schema, 3); }
    for (L->i = 0; L->i < L->p.nin + L->p.nout; L->i++) {
        FR_CALL(k, L->t, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->t, state_at(&L->p, L->i)));
    }
    if (L->t != L->p.wtype) FR_FINISH(k, prep_res(2, "the witness type is not the schema's edge type at these states", 0));
    /* the witness's proof use: the one judgment proof_use decodes */
    FR_AWAIT(k, L->ev, J_ADMIT, RQ(AD_PROOF, L->G, fc_true(), L->p.witness, L->t, 0), 0);
    if (admit_code(L->ev) == 3) FR_FINISH(k, prep_res(3, "unresolved: the edge witness", L->ev));
    if (admit_code(L->ev) != 1) FR_FINISH(k, prep_res(2, rword(L->ev, 1) ? (const char *)(uintptr_t)rword(L->ev, 1) : "the edge witness does not check", L->ev));
    if (rword(rword(L->ev, 5), 0) == PU_PENDING) FR_FINISH(k, prep_res(3, "the witness depends on a recursively pending proof", L->ev));
    /* authorization: each consumed cell's authority issued a capability the
     * proposal supplies — a head: its authority; a port: its recipient, or the
     * authority whose head its issuing occurrence consumed (a refund). One
     * input, issuing input or capability per step. */
    for (L->i = 0; L->i < L->p.nin; L->i++) {
        {   size_t n; const uint64_t *in = rget(L->p.in[L->i], &n); L->need = in[0] == T_HEAD ? in[1] : in[4]; L->issuer = 0;
            L->ip.nin = 0; if (in[0] == T_PORT) L->ip = prop_of(rget(in[1], &n)[2]); }
        for (L->j = 0; L->j < L->ip.nin; L->j++) { size_t n; const uint64_t *h = rget(L->ip.in[L->j], &n); if (h[0] == T_HEAD) L->issuer = h[1]; FR_YIELD(k); }
        for (L->ok = 0, L->c = 0; L->c < L->p.ncap && !L->ok; L->c++) {
            {   size_t n; const uint64_t *cw = rget(L->p.cap[L->c], &n);
                L->ok = cw[0] == T_CAP && (cw[1] == L->need || (L->issuer && cw[1] == L->issuer)) && interner_find(&EF.issued, &L->p.cap[L->c], 1) != 0; }
            FR_YIELD(k);
        }
        if (!L->ok) FR_FINISH(k, prep_res(2, "a consumed cell's authority issued no supplied capability", L->ev));
    }
    /* one successor head for each consumed authority, and none for another; one comparison per step */
    for (L->i = 0; L->i < L->p.nout; L->i++) {
        if (L->p.out[3 * L->i]) { FR_YIELD(k); continue; }
        for (L->cnt = 0, L->j = 0; L->j < L->p.nin; L->j++) { size_t n; const uint64_t *in = rget(L->p.in[L->j], &n); if (in[0] == T_HEAD && in[1] == L->p.out[3 * L->i + 1]) L->cnt++; FR_YIELD(k); }
        if (L->cnt != 1) FR_FINISH(k, prep_res(2, "a successor head of an authority the proposal does not consume", L->ev));
        for (L->j = 0; L->j < L->p.nout; L->j++) {
            if (L->j != L->i && !L->p.out[3 * L->j] && L->p.out[3 * L->j + 1] == L->p.out[3 * L->i + 1]) FR_FINISH(k, prep_res(2, "two successors of one authority", L->ev));
            FR_YIELD(k);
        }
    }
    for (L->i = 0; L->i < L->p.nin; L->i++) {
        {   size_t n; const uint64_t *in = rget(L->p.in[L->i], &n); L->ok = in[0] != T_HEAD; L->need = in[1]; }
        for (L->j = 0; L->j < L->p.nout && !L->ok; L->j++) { L->ok = !L->p.out[3 * L->j] && L->p.out[3 * L->j + 1] == L->need; FR_YIELD(k); }
        if (!L->ok) FR_FINISH(k, prep_res(2, "a consumed authority without its successor head", L->ev));
        FR_YIELD(k);
    }
    FR_FINISH(k, prep_res(1, NULL, L->ev));
    FR_END(k);
}

/* ---------------- EFFECT(rid, P) ---------------- */
typedef struct { Desc *D; size_t k, j, nt; uint64_t w, r, in, s, ev; Prop p; } EfLoc;
static uint64_t out_rec(Outcome o, uint64_t a) { return RQ(T_OUT, (uint64_t)o, a); }
static uint64_t *rid_slot(uint64_t rid) { return keyed_slot(&EF.rids, &rid, 1, NULL); }
static void settle(uint64_t rid, uint64_t out) { __atomic_store_n(&rid_slot(rid)[1], out, __ATOMIC_RELEASE); }
/* a commit descriptor of nt cells (one allocation) */
/* a commit descriptor and its range of nt cells (one reservation of each counter) */
static Desc *desc_alloc(uint64_t rid, uint64_t prop, uint64_t ev, size_t n, size_t nt) {
    Desc *D = chunked_at(&EF.descs, __atomic_fetch_add(&EF.ndescs, 1, __ATOMIC_RELAXED));
    D->rid = rid; D->prop = prop; D->n = n; D->nt = nt; D->occ = RQ(T_OCC, rid, prop, ev);
    D->base = __atomic_fetch_add(&EF.ndcells, nt, __ATOMIC_RELAXED);
    return D;
}
static void desc_cell(Desc *D, size_t k, uint64_t cell, uint64_t key, uint64_t expect, uint64_t after) {
    DCell *c = DC(D, k); c->cell = cell; c->ckey = key; c->expect = expect; c->after = after; c->node.D = D; c->node.k = k;
}
static void effect_step(Cont *k, uint64_t v) {
    EfLoc *L = FR_LOC(k, EfLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    /* the request index: one proposal per request id; a settled outcome is returned */
    {   uint64_t *s = rid_slot(k->w[0]), e = 0;
        if (!__atomic_compare_exchange_n(&s[0], &e, k->w[1], false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE) && e != k->w[1])
            FR_FINISH(k, out_rec(OUT_REQUEST_CONFLICT, 0));
        uint64_t settled = __atomic_load_n(&s[1], __ATOMIC_ACQUIRE);
        if (settled) FR_FINISH(k, settled); }
    FR_AWAIT(k, r, F_PREP, k->w[1], 0);
    {   size_t n; const uint64_t *w = rget(r, &n);
        if (w[1] == 3) FR_FINISH(k, out_rec(OUT_UNRESOLVED, 0));            /* pending, not settled */
        if (w[1] != 1) { uint64_t o = out_rec(OUT_INVALID, w[2]); settle(k->w[0], o); FR_FINISH(k, o); }
        L->ev = w[3]; }                                                   /* the admitted proof-use judgment */
    L->p = prop_of(k->w[1]);
    /* the commit descriptor: its inputs in reservation order (a head's
     * preconstructed successor), then its output ports; one cell or one
     * output comparison per step */
    for (L->nt = L->p.nin, L->j = 0; L->j < L->p.nout; L->j++) { if (L->p.out[3 * L->j]) L->nt++; FR_YIELD(k); }
    L->D = desc_alloc(k->w[0], k->w[1], L->ev, L->p.nin, L->nt);
    for (L->k = 0; L->k < L->D->n; L->k++) {
        L->in = L->p.in[L->p.ord[L->k]];
        {   size_t n; const uint64_t *w = rget(L->in, &n); L->w = w[0] == T_HEAD ? w[1] : 0; }
        for (L->s = 0, L->j = 0; L->w && L->j < L->p.nout; L->j++) { if (!L->p.out[3 * L->j] && L->p.out[3 * L->j + 1] == L->w) L->s = L->p.out[3 * L->j + 2]; FR_YIELD(k); }
        desc_cell(L->D, L->k, cell_kind_of(L->in), cell_id_of(L->in), W_AVAIL(L->in), L->w ? W_AVAIL(RQ(T_HEAD, L->w, L->D->occ, L->s, L->in)) : W_CONS(L->D->occ));
        FR_YIELD(k);
    }
    for (L->k = L->D->n, L->j = 0; L->j < L->p.nout; L->j++) {
        if (L->p.out[3 * L->j]) { uint64_t port = RQ(T_PORT, L->D->occ, L->j, L->p.out[3 * L->j + 2], L->p.out[3 * L->j + 1]); desc_cell(L->D, L->k++, CK_PORT, port, 0, W_AVAIL(port)); }
        FR_YIELD(k);
    }
    {   bool fresh; Desc **slot = keyed_slot(&EF.occs, &L->D->occ, 1, &fresh);
        require(fresh, "one descriptor per occurrence");
        __atomic_store_n(slot, L->D, __ATOMIC_RELEASE); }
    /* reservations: one cell per step, in the fixed total order */
    for (L->k = 0; L->k < L->D->n; ) {
        L->w = __atomic_load_n(cell_word(DC(L->D, L->k)->cell, DC(L->D, L->k)->ckey), __ATOMIC_ACQUIRE);
        if (W_TAG(L->w) == 2) {
            {   Node *nd = W_NODE(L->w); int s = __atomic_load_n(&nd->D->state, __ATOMIC_ACQUIRE);
                if (s != D_RESERVING) {                                      /* help finalize a terminal reservation, then retry */
                    uint64_t e = L->w;
                    __atomic_compare_exchange_n(cell_word(DC(L->D, L->k)->cell, DC(L->D, L->k)->ckey), &e, s == D_COMMITTED ? DC(nd->D, nd->k)->after : DC(nd->D, nd->k)->expect, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
                    L->r = 0;
                } else L->r = (uint64_t)(uintptr_t)nd->D; }
            if (!L->r) { FR_YIELD(k); continue; }
            FR_AWAIT(k, r, F_EFFECT, ((Desc *)(uintptr_t)L->r)->rid, ((Desc *)(uintptr_t)L->r)->prop);   /* its own progress owner */
            continue;
        }
        if (L->w != DC(L->D, L->k)->expect) break;                               /* absent, stale or consumed: a conflict */
        {   uint64_t e = L->w;
            if (__atomic_compare_exchange_n(cell_word(DC(L->D, L->k)->cell, DC(L->D, L->k)->ckey), &e, W_RES(&DC(L->D, L->k)->node), false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) L->k++; }
        FR_YIELD(k);
    }
    if (L->k == L->D->n)
        for (; L->k < L->D->nt; L->k++) {                                /* output ports: visible exactly at the commit */
            {   uint64_t e = 0;
                if (!__atomic_compare_exchange_n(cell_word(DC(L->D, L->k)->cell, DC(L->D, L->k)->ckey), &e, W_RES(&DC(L->D, L->k)->node), false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) break; }
            FR_YIELD(k);
        }
    if (L->k < L->D->nt) {
        __atomic_store_n(&L->D->state, D_ABORTED, __ATOMIC_RELEASE);
        for (L->j = 0; L->j < L->k; L->j++) {                                /* rollback, one cell per step */
            {   uint64_t e = W_RES(&DC(L->D, L->j)->node);
                __atomic_compare_exchange_n(cell_word(DC(L->D, L->j)->cell, DC(L->D, L->j)->ckey), &e, DC(L->D, L->j)->expect, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE); }
            FR_YIELD(k);
        }
        {   uint64_t o = out_rec(OUT_CONFLICT, RQ(DC(L->D, L->k)->cell, DC(L->D, L->k)->ckey)); settle(k->w[0], o); FR_FINISH(k, o); }
    }
    /* the one acceptance event */
    __atomic_store_n(&L->D->state, D_COMMITTED, __ATOMIC_RELEASE);
    for (L->j = 0; L->j < L->D->nt; L->j++) {                                 /* finalization, one cell per step */
        {   uint64_t e = W_RES(&DC(L->D, L->j)->node);
            __atomic_compare_exchange_n(cell_word(DC(L->D, L->j)->cell, DC(L->D, L->j)->ckey), &e, DC(L->D, L->j)->after, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE); }
        FR_YIELD(k);
    }
    {   uint64_t o = out_rec(OUT_ACCEPTED, L->D->occ); settle(k->w[0], o); FR_FINISH(k, o); }
    FR_END(k);
}

/* occurrence.boundary(E): ∂_res[E] = produced − consumed, over heads and ports */
static Desc *desc_of(uint64_t occ) { Desc **d = keyed_find(&EF.occs, &occ, 1); return d ? __atomic_load_n(d, __ATOMIC_ACQUIRE) : NULL; }
typedef struct { Desc *D; Prop p; size_t i; uint64_t acc, in, k; } ObLoc;
static void occb_step(Cont *k, uint64_t v) {
    ObLoc *L = FR_LOC(k, ObLoc);
    FR_BEGIN(k);
    L->D = desc_of(k->w[0]);
    require(L->D && __atomic_load_n(&L->D->state, __ATOMIC_ACQUIRE) == D_COMMITTED, "the resource boundary of an unaccepted occurrence");
    L->p = prop_of(L->D->prop);
    L->acc = RQ(0);
    /* one term per step: each consumed cell −1, a head's successor +1, each output port +1 */
    for (L->i = 0; L->i < L->D->n; L->i++) {
        L->in = W_VAL(DC(L->D, L->i)->expect);
        {   size_t m; L->k = rget(L->in, &m)[0] == T_HEAD; }
        FR_AWAIT(k, L->acc, Fc_ADD, L->acc, RQ(0, L->k ? G_HEAD : G_PORT, L->in, z_from_i64(-1)));
        if (L->k) FR_AWAIT(k, L->acc, Fc_ADD, L->acc, RQ(0, G_HEAD, W_VAL(DC(L->D, L->i)->after), z_from_i64(1)));
    }
    for (L->i = L->D->n; L->i < L->D->nt; L->i++) FR_AWAIT(k, L->acc, Fc_ADD, L->acc, RQ(0, G_PORT, DC(L->D, L->i)->ckey, z_from_i64(1)));
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- readers ---------------- */
uint64_t effect_head(uint64_t authority) { uint64_t w = cell_logical(CK_HEAD, authority); return W_TAG(w) == 1 ? W_VAL(w) : 0; }
RefId head_state(uint64_t head) { return rword(head, 3); }
uint64_t head_occurrence(uint64_t head) { return rword(head, 2); }
uint64_t effect_port(uint64_t occurrence, size_t slot) {
    Desc *D = desc_of(occurrence); if (!D) return 0;
    Prop p = prop_of(D->prop);
    if (slot >= p.nout || !p.out[3 * slot]) return 0;
    return RQ(T_PORT, occurrence, slot, p.out[3 * slot + 2], p.out[3 * slot + 1]);
}
int port_status(uint64_t port, uint64_t *consumer) {
    uint64_t w = cell_logical(CK_PORT, port);
    if (W_TAG(w) == 1) return 1;
    if (W_TAG(w) == 3) { if (consumer) *consumer = W_VAL(w); return 2; }
    return 0;
}
RefId port_payload(uint64_t port) { return rword(port, 3); }
size_t effect_open_ports(uint64_t *out, size_t max) {
    size_t nc = interner_count(&EF.cells.keys), k = 0;
    for (size_t c = 1; c <= nc; c++) {
        if (!interner_live(&EF.cells.keys, c)) continue;
        size_t n; const uint64_t *key = interner_get(&EF.cells.keys, c, &n);
        if (key[0] != CK_PORT) continue;
        uint64_t *wp = chunked_peek(&EF.cells.slots, c - 1); if (!wp) continue;
        uint64_t w = logical(__atomic_load_n(wp, __ATOMIC_ACQUIRE));
        if (W_TAG(w) == 1) { if (k < max) out[k] = W_VAL(w); k++; }
    }
    return k;
}
bool receipt_accepted(uint64_t occurrence) { Desc *D = desc_of(occurrence); return D && __atomic_load_n(&D->state, __ATOMIC_ACQUIRE) == D_COMMITTED; }
uint64_t receipt_proposal(uint64_t occurrence) { return rword(occurrence, 2); }
uint64_t receipt_evidence(uint64_t occurrence) { return rword(occurrence, 3); }
/* the context of the free variables of a few references, in declaration order */
static ContextId fv_context(size_t n, const RefId *refs) {
    VarSetId fv = set_make(NULL, 0);
    for (size_t i = 0; i < n; i++) if (refs[i]) fv = set_union(fv, ref_freevars(refs[i]));
    size_t m; const uint64_t *w = set_get(fv, &m);
    CtxDecl *d = malloc((m ? m : 1) * sizeof *d); require(d, "out of memory");
    for (size_t i = 0; i < m; i++) { d[i].sort = S_TERM; d[i].id = w[i]; }
    ContextId G = context_make(m, d, fc_true()); free(d);
    return G;
}
uint64_t receipt_view(uint64_t occurrence, MapId sigma, uint64_t eta) {
    if (!receipt_accepted(occurrence)) return 0;
    Prop p = prop_of(receipt_proposal(occurrence));
    RefId S = rword(p.schema, 1); uint64_t l = rword(p.schema, 2);
    /* each boundary state σ moves needs its transport η_i : Path S s_i s_i[σ],
     * checked; the event — its occurrence, authorities and port anchors — is
     * unchanged; the identity transport is the stationary case */
    for (size_t i = 0; i < p.nin + p.nout; i++) {
        RefId s = state_at(&p, i), t = reindex(s, sigma);
        if (t == s) continue;
        uint64_t r = eta ? family_call(F_LOOKUP, eta, i) : 0;
        if (!r) return 0;
        RefId w = subst_value(eta, r - 1), refs[3] = { s, t, w }; const char *why;
        if (check(fv_context(3, refs), fc_true(), w, mk_path_const(l, S, s, t), &why) != CK_VALID) return 0;
    }
    return RQ(T_VIEW, occurrence, sigma, eta);
}
uint64_t receipt_view_occurrence(uint64_t view) { size_t n; const uint64_t *w = rget(view, &n); return w[0] == T_VIEW ? w[1] : 0; }

/* λX. λf. λx. f^n x  ↦  n: a checked word projection (false when n is not
 * such a numeral or exceeds the word) */
bool church_value(RefId n, uint64_t *out) {
    WhnfStatus st; RefId U = mk_universe(0);
    TermVarId vX = declare_term(U, fc_true()); RefId X = ref_var(vX);
    TermVarId vf = declare_term(mk_fun(0, 0, X, X), fc_true()); RefId f = ref_var(vf);
    TermVarId vx = declare_term(X, fc_true()); RefId x = ref_var(vx);
    RefId args[3] = { X, f, x }; RefId t = n;
    for (int q = 0; q < 3; q++) {
        EvalResult r = whnf(t, fc_true(), &st);
        if (st != W_OK || r.cls != R_INTRODUCTION || ref_tag(r.ref) != T_LAM) return false;
        t = apply_term_binder(r.ref, 0, 1, args[q]);
    }
    uint64_t c = 0;
    for (;;) {
        EvalResult r = whnf(t, fc_true(), &st);
        if (st != W_OK) return false;
        if (r.ref == x) { *out = c; return true; }
        if (ref_is_var(r.ref) || ref_tag(r.ref) != T_APP) return false;
        Head h; open_ref(r.ref, &h);
        if (HF(&h, 0).id != f) { head_free(&h); return false; }
        t = HF(&h, 1).id; head_free(&h);
        if (c == UINT64_MAX) return false;              /* beyond the word: out of range, never wrapped */
        c++;
    }
}

uint64_t effect_request(uint64_t rid, uint64_t proposal, WhnfStatus *status) { return family_run(F_EFFECT, rid, proposal, status); }
Family effect_family(void) { return F_EFFECT; }

void effect_state_init(void) {
    keyed_init(&EF.cells, sizeof(uint64_t));
    keyed_init(&EF.rids, 2 * sizeof(uint64_t));
    interner_init(&EF.issued);
    keyed_init(&EF.occs, sizeof(Desc *));
    chunked_init(&EF.descs, sizeof(Desc)); chunked_init(&EF.dcells, sizeof(DCell)); EF.ndescs = EF.ndcells = 0;
}
void effect_families_init(void) {
    family_define(F_PREP, "effect.prepare", prep_step, sizeof(PrLoc));
    family_define(F_EFFECT, "effect.request", effect_step, sizeof(EfLoc));
    family_define(F_OCCB, "occurrence.boundary", occb_step, sizeof(ObLoc));
}
void effect_state_free(void) {
    keyed_free(&EF.cells); keyed_free(&EF.rids); interner_free(&EF.issued); keyed_free(&EF.occs);
    chunked_free(&EF.descs); chunked_free(&EF.dcells);
}
