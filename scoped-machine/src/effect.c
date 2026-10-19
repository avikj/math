/* effect.c — witnessed effects, authority and ports (effect.h). */
#include "effect.h"
#include "judge.h"
#include "pins.h"
#include "proof.h"
#include "chain.h"
#include "lib.h"

enum { T_SCHEMA = 0xEF01, T_AUTH, T_HEAD, T_PORT, T_CAP, T_PROP, T_OCC, T_PREP, T_OUT, T_VIEW };
enum { CK_HEAD = 1, CK_PORT };
static uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
static const uint64_t *rget(uint64_t id, size_t *n) { return interner_get(&M.keys, id, n); }
#define RQ(...) rq(sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ })

/* ---------------- cells and descriptors ---------------- */
typedef struct Desc Desc;
typedef struct { Desc *D; size_t k; } Node;
enum { D_RESERVING = 0, D_COMMITTED, D_ABORTED };
struct Desc {
    int state;                          /* the one acceptance point: RESERVING → COMMITTED | ABORTED */
    uint64_t rid, prop, occ;
    size_t n;                           /* inputs, in reservation order */
    size_t nt;                          /* inputs, then output port cells (expect absent, after the port) */
    uint64_t *cell, *ckey, *expect, *after;
    Node *nodes;
};
/* a cell word: 0 absent | AVAILABLE(x) | RESERVED(node) | CONSUMED(occurrence) */
#define W_AVAIL(x) (((uint64_t)(x) << 2) | 1)
#define W_CONS(o) (((uint64_t)(o) << 2) | 3)
#define W_RES(nd) ((uint64_t)(uintptr_t)(nd) | 2)
#define W_TAG(w) ((w) & 3)
#define W_VAL(w) ((w) >> 2)
#define W_NODE(w) ((Node *)(uintptr_t)((w) & ~(uint64_t)3))

static struct {
    Interner cells; Chunked cellw;      /* [kind, id] → its word */
    Interner rids; Chunked ridw;        /* request id → [proposal, settled outcome] */
    Interner issued;                    /* capabilities an authority issued */
    Interner occs; Chunked occd;        /* occurrence → its descriptor */
} EF;

static uint64_t *cell_word(uint64_t kind, uint64_t id) {
    uint64_t w[2] = { kind, id };
    uint64_t c = interner_intern(&EF.cells, w, 2, NULL);
    return chunked_at(&EF.cellw, c - 1);
}
/* the logical value of a cell: a reservation read through its descriptor */
static uint64_t logical(uint64_t w) {
    if (W_TAG(w) != 2) return w;
    Node *nd = W_NODE(w);
    int s = __atomic_load_n(&nd->D->state, __ATOMIC_ACQUIRE);
    return s == D_COMMITTED ? nd->D->after[nd->k] : nd->D->expect[nd->k];
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
static uint64_t cell_kind_of(uint64_t rec) { size_t n; return rget(rec, &n)[0] == T_HEAD ? CK_HEAD : CK_PORT; }
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
Outcome outcome_kind(uint64_t out) { size_t n; return (Outcome)rget(out, &n)[1]; }
uint64_t outcome_occurrence(uint64_t out) { size_t n; const uint64_t *w = rget(out, &n); return w[1] == OUT_ACCEPTED ? w[2] : 0; }
const char *outcome_reason(uint64_t out) { size_t n; const uint64_t *w = rget(out, &n); return w[1] == OUT_INVALID ? (const char *)(uintptr_t)w[2] : ""; }

static Family F_PREP, F_EFFECT, F_OCCB, Fe_JCHECK, Fe_JLEVEL, Fe_CONSTRUCT, Fe_SCC, Fe_CLOSURE;

/* ---------------- PREPARE(P) ---------------- */
typedef struct { size_t i, j; uint64_t P, t, r; Prop p; const char *bad; WordBuf wb; bool created; } PrLoc;
static uint64_t prep_res(int ok, const char *why) { return RQ(T_PREP, (uint64_t)ok, (uint64_t)(uintptr_t)why); }
static uint64_t state_at(const Prop *p, size_t i) { return i < p->nin ? value_of(p->in[i]) : p->out[3 * (i - p->nin) + 2]; }
static void prep_step(Cont *k, uint64_t v) {
    PrLoc *L = FR_LOC(k, PrLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->p = prop_of(k->w[0]);
    /* the premises: the closure of the schema, the states and the witness at
     * the snapshot this key names (w[1]) */
    {   size_t n; const uint64_t *sc = rget(L->p.schema, &n); require(sc[0] == T_SCHEMA, "a proposal without a schema");
        wordbuf_init(&L->wb);
        wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, sc[1]); wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, sc[3]); }
    for (L->i = 0; L->i < L->p.nin + L->p.nout; L->i++) { wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, state_at(&L->p, L->i)); FR_YIELD(k); }
    wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, L->p.witness); wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, L->p.wtype);
    FR_CALL(k, L->r, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_AWAIT(k, L->P, Fe_CLOSURE, L->r, k->w[1]);
    /* the state type at its declared level, exactly */
    {   size_t n; const uint64_t *sc = rget(L->p.schema, &n); L->t = sc[1]; L->r = sc[2]; }
    FR_AWAIT(k, r, Fe_JLEVEL, RQ(fc_true(), L->t, L->P), 0);
    if (jr_code(r) != 1) FR_FINISH(k, prep_res(jr_code(r) == 3 ? 3 : 2, "the state type is not a type"));
    if (jr_a(r) != L->r) FR_FINISH(k, prep_res(2, "the state type is not at its declared level"));
    /* every input and output state at the state type */
    for (L->i = 0; L->i < L->p.nin + L->p.nout; L->i++) {
        FR_AWAIT(k, r, Fe_JCHECK, RQ(fc_true(), state_at(&L->p, L->i), L->t, L->P), 0);
        if (jr_code(r) != 1) FR_FINISH(k, prep_res(jr_code(r) == 3 ? 3 : 2, "a state is not of the state type"));
    }
    /* the witness type is R at the states, built here through the construction family */
    {   size_t n; L->t = rget(L->p.schema, &n)[3]; }
    for (L->i = 0; L->i < L->p.nin + L->p.nout; L->i++) {
        FR_AWAIT(k, L->t, Fe_CONSTRUCT, RQ(T_APP, 0, LEVELS_NONE, 0, 0, 0, 2, F_REF, NO_SLOT, L->t, F_REF, NO_SLOT, state_at(&L->p, L->i), 0), 0);
    }
    if (L->t != L->p.wtype) FR_FINISH(k, prep_res(2, "the witness type is not the schema's edge type at these states"));
    FR_AWAIT(k, r, Fe_JLEVEL, RQ(fc_true(), L->t, L->P), 0);
    if (jr_code(r) != 1) FR_FINISH(k, prep_res(jr_code(r) == 3 ? 3 : 2, "the edge type is not a type"));
    FR_AWAIT(k, r, Fe_JCHECK, RQ(fc_true(), L->p.witness, L->t, L->P), 0);
    if (jr_code(r) == 3) FR_FINISH(k, prep_res(3, "unresolved: the edge witness"));
    if (jr_code(r) != 1) FR_FINISH(k, prep_res(2, jr_why(r) ? jr_why(r) : "the edge witness does not check"));
    /* proof use: a recursively pending witness is not admitted */
    if (pins_symbols(L->P, NULL, 0)) {
        {   size_t ns = pins_symbols(L->P, NULL, 0); SymbolId *ss = malloc(ns * sizeof *ss); require(ss, "out of memory");
            pins_symbols(L->P, ss, ns); L->r = varset_make(ss, ns); free(ss); }
        FR_AWAIT(k, r, Fe_SCC, L->P, L->r);
        {   size_t n; if (rget(r, &n)[0] == PU_PENDING) FR_FINISH(k, prep_res(3, "the witness depends on a recursively pending proof")); }
    }
    /* authorization: each consumed cell's authority issued a capability the proposal supplies */
    for (L->i = 0; L->i < L->p.nin; L->i++) {
        {   size_t n; const uint64_t *in = rget(L->p.in[L->i], &n);
            /* a head: its authority; a port: its recipient, or the authority whose
             * head its issuing occurrence consumed (a refund) */
            uint64_t need = in[0] == T_HEAD ? in[1] : in[4], issuer = 0; bool ok = false;
            if (in[0] == T_PORT) { Prop ip = prop_of(rget(in[1], &n)[2]); for (size_t j = 0; j < ip.nin; j++) { const uint64_t *h = rget(ip.in[j], &n); if (h[0] == T_HEAD) issuer = h[1]; } }
            for (size_t c = 0; c < L->p.ncap && !ok; c++) {
                const uint64_t *cw = rget(L->p.cap[c], &n);
                ok = cw[0] == T_CAP && (cw[1] == need || (issuer && cw[1] == issuer)) && interner_find(&EF.issued, &L->p.cap[c], 1) != 0;
            }
            if (!ok) FR_FINISH(k, prep_res(2, "a consumed cell's authority issued no supplied capability")); }
        FR_YIELD(k);
    }
    /* one successor head for each consumed authority, and none for another */
    for (L->i = 0; L->i < L->p.nout; L->i++) {
        if (!L->p.out[3 * L->i]) {
            size_t c = 0;
            for (size_t j = 0; j < L->p.nin; j++) { size_t n; const uint64_t *in = rget(L->p.in[j], &n); if (in[0] == T_HEAD && in[1] == L->p.out[3 * L->i + 1]) c++; }
            if (c != 1) FR_FINISH(k, prep_res(2, "a successor head of an authority the proposal does not consume"));
            for (size_t j = 0; j < L->p.nout; j++) if (j != L->i && !L->p.out[3 * j] && L->p.out[3 * j + 1] == L->p.out[3 * L->i + 1]) FR_FINISH(k, prep_res(2, "two successors of one authority"));
        }
        FR_YIELD(k);
    }
    for (L->i = 0; L->i < L->p.nin; L->i++) {
        {   size_t n; const uint64_t *in = rget(L->p.in[L->i], &n); bool found = in[0] != T_HEAD;
            for (size_t j = 0; j < L->p.nout && !found; j++) found = !L->p.out[3 * j] && L->p.out[3 * j + 1] == in[1];
            if (!found) FR_FINISH(k, prep_res(2, "a consumed authority without its successor head")); }
        FR_YIELD(k);
    }
    FR_FINISH(k, prep_res(1, NULL));
    FR_END(k);
}

/* ---------------- EFFECT(rid, P) ---------------- */
typedef struct { Desc *D; size_t k, j; uint64_t w, r; Prop p; } EfLoc;
static uint64_t out_rec(Outcome o, uint64_t a) { return RQ(T_OUT, (uint64_t)o, a); }
static uint64_t *rid_slot(uint64_t rid) { uint64_t c = interner_intern(&EF.rids, &rid, 1, NULL); return chunked_at(&EF.ridw, c - 1); }
static void settle(uint64_t rid, uint64_t out) { __atomic_store_n(&rid_slot(rid)[1], out, __ATOMIC_RELEASE); }
static Desc *desc_new(uint64_t rid, uint64_t prop, const Prop *p) {
    Desc *D = calloc(1, sizeof *D); require(D, "out of memory: a commit descriptor");
    D->rid = rid; D->prop = prop; D->n = p->nin; D->nt = p->nin;
    for (size_t j = 0; j < p->nout; j++) if (p->out[3 * j]) D->nt++;
    D->cell = calloc(D->nt + 1, sizeof *D->cell); D->ckey = calloc(D->nt + 1, sizeof *D->ckey);
    D->expect = calloc(D->nt + 1, sizeof *D->expect); D->after = calloc(D->nt + 1, sizeof *D->after);
    D->nodes = calloc(D->nt + 1, sizeof *D->nodes);
    require(D->cell && D->ckey && D->expect && D->after && D->nodes, "out of memory: a commit descriptor");
    D->occ = RQ(T_OCC, rid, prop);
    for (size_t k = 0; k < D->n; k++) {
        uint64_t in = p->in[p->ord[k]];
        size_t n; const uint64_t *w = rget(in, &n);
        D->cell[k] = cell_kind_of(in); D->ckey[k] = cell_id_of(in);
        D->expect[k] = W_AVAIL(in);
        D->nodes[k].D = D; D->nodes[k].k = k;
        if (w[0] == T_HEAD) {
            RefId s = 0; for (size_t j = 0; j < p->nout; j++) if (!p->out[3 * j] && p->out[3 * j + 1] == w[1]) s = p->out[3 * j + 2];
            D->after[k] = W_AVAIL(RQ(T_HEAD, w[1], D->occ, s, in));        /* the preconstructed successor */
        } else D->after[k] = W_CONS(D->occ);
    }
    for (size_t j = 0, k = D->n; j < p->nout; j++) if (p->out[3 * j]) {
        uint64_t port = RQ(T_PORT, D->occ, j, p->out[3 * j + 2], p->out[3 * j + 1]);
        D->cell[k] = CK_PORT; D->ckey[k] = port; D->expect[k] = 0; D->after[k] = W_AVAIL(port);
        D->nodes[k].D = D; D->nodes[k].k = k; k++;
    }
    bool fresh; uint64_t c = interner_intern(&EF.occs, &D->occ, 1, &fresh);
    require(fresh, "one descriptor per occurrence");
    __atomic_store_n((Desc **)chunked_at(&EF.occd, c - 1), D, __ATOMIC_RELEASE);
    return D;
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
    FR_AWAIT(k, r, F_PREP, k->w[1], env_snapshot());
    {   size_t n; const uint64_t *w = rget(r, &n);
        if (w[1] == 3) FR_FINISH(k, out_rec(OUT_UNRESOLVED, 0));            /* pending, not settled */
        if (w[1] != 1) { uint64_t o = out_rec(OUT_INVALID, w[2]); settle(k->w[0], o); FR_FINISH(k, o); } }
    L->p = prop_of(k->w[1]);
    L->D = desc_new(k->w[0], k->w[1], &L->p);
    /* reservations: one cell per step, in the fixed total order */
    for (L->k = 0; L->k < L->D->n; ) {
        L->w = __atomic_load_n(cell_word(L->D->cell[L->k], L->D->ckey[L->k]), __ATOMIC_ACQUIRE);
        if (W_TAG(L->w) == 2) {
            {   Node *nd = W_NODE(L->w); int s = __atomic_load_n(&nd->D->state, __ATOMIC_ACQUIRE);
                if (s != D_RESERVING) {                                      /* help finalize a terminal reservation, then retry */
                    uint64_t e = L->w;
                    __atomic_compare_exchange_n(cell_word(L->D->cell[L->k], L->D->ckey[L->k]), &e, s == D_COMMITTED ? nd->D->after[nd->k] : nd->D->expect[nd->k], false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
                    L->r = 0;
                } else L->r = (uint64_t)(uintptr_t)nd->D; }
            if (!L->r) { FR_YIELD(k); continue; }
            FR_AWAIT(k, r, F_EFFECT, ((Desc *)(uintptr_t)L->r)->rid, ((Desc *)(uintptr_t)L->r)->prop);   /* its own progress owner */
            continue;
        }
        if (L->w != L->D->expect[L->k]) break;                               /* absent, stale or consumed: a conflict */
        {   uint64_t e = L->w;
            if (__atomic_compare_exchange_n(cell_word(L->D->cell[L->k], L->D->ckey[L->k]), &e, W_RES(&L->D->nodes[L->k]), false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) L->k++; }
        FR_YIELD(k);
    }
    if (L->k == L->D->n)
        for (; L->k < L->D->nt; L->k++) {                                /* output ports: visible exactly at the commit */
            {   uint64_t e = 0;
                if (!__atomic_compare_exchange_n(cell_word(L->D->cell[L->k], L->D->ckey[L->k]), &e, W_RES(&L->D->nodes[L->k]), false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) break; }
            FR_YIELD(k);
        }
    if (L->k < L->D->nt) {
        __atomic_store_n(&L->D->state, D_ABORTED, __ATOMIC_RELEASE);
        for (L->j = 0; L->j < L->k; L->j++) {                                /* rollback, one cell per step */
            {   uint64_t e = W_RES(&L->D->nodes[L->j]);
                __atomic_compare_exchange_n(cell_word(L->D->cell[L->j], L->D->ckey[L->j]), &e, L->D->expect[L->j], false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE); }
            FR_YIELD(k);
        }
        {   uint64_t o = out_rec(OUT_CONFLICT, RQ(L->D->cell[L->k], L->D->ckey[L->k])); settle(k->w[0], o); FR_FINISH(k, o); }
    }
    /* the one acceptance event */
    __atomic_store_n(&L->D->state, D_COMMITTED, __ATOMIC_RELEASE);
    for (L->j = 0; L->j < L->D->nt; L->j++) {                                 /* finalization, one cell per step */
        {   uint64_t e = W_RES(&L->D->nodes[L->j]);
            __atomic_compare_exchange_n(cell_word(L->D->cell[L->j], L->D->ckey[L->j]), &e, L->D->after[L->j], false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE); }
        FR_YIELD(k);
    }
    {   uint64_t o = out_rec(OUT_ACCEPTED, L->D->occ); settle(k->w[0], o); FR_FINISH(k, o); }
    FR_END(k);
}

/* occurrence.boundary(E): ∂_res[E] = produced − consumed, over heads and ports */
static Desc *desc_of(uint64_t occ) {
    uint64_t c = interner_find(&EF.occs, &occ, 1);
    if (!c) return NULL;
    Desc **d = chunked_peek(&EF.occd, c - 1);
    return d ? __atomic_load_n(d, __ATOMIC_ACQUIRE) : NULL;
}
static void occb_step(Cont *k, uint64_t v) {
    FR_BEGIN(k);
    {   Desc *D = desc_of(k->w[0]);
        require(D && __atomic_load_n(&D->state, __ATOMIC_ACQUIRE) == D_COMMITTED, "the resource boundary of an unaccepted occurrence");
        Prop p = prop_of(D->prop);
        size_t n = 0, cap = 2 * D->n + p.nout + 1;
        GenKind *ks = malloc(cap * sizeof *ks); uint64_t *ids = malloc(cap * sizeof *ids), *zs = malloc(cap * sizeof *zs);
        require(ks && ids && zs, "out of memory");
        for (size_t i = 0; i < D->n; i++) {
            uint64_t in = W_VAL(D->expect[i]); size_t m; bool head = rget(in, &m)[0] == T_HEAD;
            ks[n] = head ? G_HEAD : G_PORT; ids[n] = in; zs[n] = z_from_i64(-1); n++;
            if (head) { ks[n] = G_HEAD; ids[n] = W_VAL(D->after[i]); zs[n] = z_from_i64(1); n++; }
        }
        for (size_t j = 0; j < p.nout; j++) if (p.out[3 * j]) { ks[n] = G_PORT; ids[n] = RQ(T_PORT, D->occ, j, p.out[3 * j + 2], p.out[3 * j + 1]); zs[n] = z_from_i64(1); n++; }
        uint64_t c = chain_of(0, n, ks, ids, zs);
        free(ks); free(ids); free(zs);
        FR_FINISH(k, c); }
    FR_END(k);
}

/* ---------------- readers ---------------- */
uint64_t effect_head(uint64_t authority) { uint64_t w = cell_logical(CK_HEAD, authority); return W_TAG(w) == 1 ? W_VAL(w) : 0; }
RefId head_state(uint64_t head) { size_t n; return rget(head, &n)[3]; }
uint64_t head_occurrence(uint64_t head) { size_t n; return rget(head, &n)[2]; }
uint64_t head_authority(uint64_t head) { size_t n; return rget(head, &n)[1]; }
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
RefId port_payload(uint64_t port) { size_t n; return rget(port, &n)[3]; }
size_t effect_open_ports(uint64_t *out, size_t max) {
    size_t nc = interner_count(&EF.cells), k = 0;
    for (size_t c = 1; c <= nc; c++) {
        if (!interner_live(&EF.cells, c)) continue;
        size_t n; const uint64_t *key = interner_get(&EF.cells, c, &n);
        if (key[0] != CK_PORT) continue;
        uint64_t *wp = chunked_peek(&EF.cellw, c - 1); if (!wp) continue;
        uint64_t w = logical(__atomic_load_n(wp, __ATOMIC_ACQUIRE));
        if (W_TAG(w) == 1) { if (k < max) out[k] = W_VAL(w); k++; }
    }
    return k;
}
bool receipt_accepted(uint64_t occurrence) { Desc *D = desc_of(occurrence); return D && __atomic_load_n(&D->state, __ATOMIC_ACQUIRE) == D_COMMITTED; }
uint64_t receipt_proposal(uint64_t occurrence) { size_t n; return rget(occurrence, &n)[2]; }
uint64_t receipt_view(uint64_t occurrence, MapId sigma) {
    if (!receipt_accepted(occurrence)) return 0;
    Prop p = prop_of(receipt_proposal(occurrence));
    /* the anchored boundary — consumed states and payloads, produced values
     * and the edge witness — is unmoved by σ, or the view is not of this event */
    for (size_t i = 0; i < p.nin + p.nout; i++) { RefId s = state_at(&p, i); if (reindex(s, sigma) != s) return 0; }
    if (reindex(p.witness, sigma) != p.witness) return 0;
    return RQ(T_VIEW, occurrence, sigma);
}
uint64_t receipt_view_occurrence(uint64_t view) { size_t n; const uint64_t *w = rget(view, &n); return w[0] == T_VIEW ? w[1] : 0; }

/* λX. λf. λx. f^n x  ↦  n */
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
        c++;
    }
}

uint64_t effect_request(uint64_t rid, uint64_t proposal, WhnfStatus *status) { return family_run(F_EFFECT, rid, proposal, status); }
Family effect_family(void) { return F_EFFECT; }

void effect_state_init(void) {
    interner_init(&EF.cells); chunked_init(&EF.cellw, sizeof(uint64_t));
    interner_init(&EF.rids); chunked_init(&EF.ridw, 2 * sizeof(uint64_t));
    interner_init(&EF.issued);
    interner_init(&EF.occs); chunked_init(&EF.occd, sizeof(Desc *));
}
void effect_families_init(void) {
    Fe_CLOSURE = pins_closure_family();
    Fe_JCHECK = family_lookup("judge.check"); Fe_JLEVEL = family_lookup("judge.level");
    Fe_CONSTRUCT = family_lookup("construct"); Fe_SCC = family_lookup("proof.scc");
    require(Fe_JCHECK && Fe_JLEVEL && Fe_CONSTRUCT && Fe_SCC, "the judgment, construction and proof-use families are registered first");
    F_PREP = family_define("effect.prepare", prep_step, sizeof(PrLoc));
    F_EFFECT = family_define("effect.request", effect_step, sizeof(EfLoc));
    F_OCCB = family_define("occurrence.boundary", occb_step, 0);
}
void effect_state_free(void) {
    for (size_t c = 0, n = interner_count(&EF.occs); c < n; c++) {     /* every descriptor is indexed by its occurrence */
        Desc **p = chunked_peek(&EF.occd, c), *D = p ? *p : NULL;
        if (D) { free(D->cell); free(D->ckey); free(D->expect); free(D->after); free(D->nodes); free(D); }
    }
    interner_free(&EF.cells); chunked_free(&EF.cellw);
    interner_free(&EF.rids); chunked_free(&EF.ridw);
    interner_free(&EF.issued);
    interner_free(&EF.occs); chunked_free(&EF.occd);
}
