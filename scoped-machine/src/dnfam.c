/* dnfam.c — sets, intervals and faces as pure producer families.
 *
 * Every operation on interned operands is a producer keyed by (family,
 * operands) in the one protocol. Each step reads, compares or appends a
 * constant number of words: clause positions are cursors in the frame's
 * locals, results are appended one word per step into a word buffer and
 * inserted by the interning subroutine, and a canonical result that needs
 * normalization is the fold of the keyed join over its clauses.
 *
 * Canonical DNF (dnf.h): clauses separated by DNF_SEP, sorted by (length,
 * lexicographic), no clause contained in another; a face has no clause with
 * both (i=0) and (i=1). The join of two canonical DNFs is their merge in
 * that order, keeping a clause unless the other operand has a proper subset
 * of it (an operand is already an antichain). */
#include "eval.h"

typedef enum { DK_IV = 0, DK_FC = 1 } DKind;
static bool rec_one(const uint64_t *w, size_t n) { return n == 1 && w[0] == DNF_SEP; }

/* ---------------- join ---------------- */
typedef struct {
    const uint64_t *x, *y; size_t nx, ny;
    size_t px, py;              /* the heads of the two operands */
    size_t i; int lex, cmp;     /* head comparison */
    const uint64_t *c, *o; size_t pc, lc, no; bool from_x;   /* candidate clause and the other operand */
    size_t q, k, m, len; bool absorbed, stop;               /* absorption scan */
    WordBuf out; bool created;
} JoinLoc;

static void join_step(Cont *k, uint64_t v) {
    JoinLoc *L = FR_LOC(k, JoinLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    if (k->w[0] == k->w[1]) FR_FINISH(k, k->w[0]);
    L->x = rget(k->w[0], &L->nx); L->y = rget(k->w[1], &L->ny);
    if (L->nx == 0 || rec_one(L->y, L->ny)) FR_FINISH(k, k->w[1]);
    if (L->ny == 0 || rec_one(L->x, L->nx)) FR_FINISH(k, k->w[0]);
    wordbuf_init(&L->out); L->px = L->py = 0;
    while (L->px < L->nx || L->py < L->ny) {
        if (L->px == L->nx) L->from_x = false;
        else if (L->py == L->ny) L->from_x = true;
        else {
            /* compare the heads by (length, lexicographic), one atom per step */
            L->lex = 0;
            for (L->i = 0;; L->i++) {
                uint64_t a = L->x[L->px + L->i], b = L->y[L->py + L->i];
                if (a == DNF_SEP && b == DNF_SEP) { L->cmp = L->lex; break; }
                if (a == DNF_SEP) { L->cmp = -1; break; }
                if (b == DNF_SEP) { L->cmp = 1; break; }
                if (!L->lex && a != b) L->lex = a < b ? -1 : 1;
                FR_YIELD(k);
            }
            if (L->cmp == 0) {
                /* the same clause in both: kept once (neither operand has a
                 * proper subset of it, or it would not be in the other) */
                for (L->i = 0; L->x[L->px + L->i] != DNF_SEP; L->i++) { wordbuf_push(&L->out, L->x[L->px + L->i]); FR_YIELD(k); }
                wordbuf_push(&L->out, DNF_SEP);
                L->px += L->i + 1; L->py += L->i + 1;
                continue;
            }
            L->from_x = L->cmp < 0;
        }
        if (L->from_x) { L->c = L->x; L->pc = L->px; L->o = L->y; L->no = L->ny; }
        else { L->c = L->y; L->pc = L->py; L->o = L->x; L->no = L->nx; }
        for (L->lc = 0; L->c[L->pc + L->lc] != DNF_SEP; L->lc++) FR_YIELD(k);
        /* absorption: a clause of the other operand properly contained in the
         * candidate; the other operand is sorted by length, so the scan stops
         * at its first clause of length ≥ lc */
        L->absorbed = false; L->stop = false; L->q = 0;
        while (L->q < L->no && !L->absorbed && !L->stop) {
            L->k = 0; L->m = 0;
            for (;;) {
                uint64_t a = L->o[L->q + L->k];
                if (a == DNF_SEP) { L->absorbed = true; break; }
                if (L->k >= L->lc) { L->stop = true; break; }
                uint64_t b = L->m < L->lc ? L->c[L->pc + L->m] : DNF_SEP;
                if (b == a) { L->k++; L->m++; }
                else if (b < a) L->m++;
                else {
                    /* not a subset: skip the rest of this clause, measuring it */
                    for (L->len = L->k; L->o[L->q + L->len] != DNF_SEP; L->len++) FR_YIELD(k);
                    if (L->len >= L->lc) L->stop = true;
                    L->q += L->len + 1;
                    break;
                }
                FR_YIELD(k);
            }
            FR_YIELD(k);
        }
        if (!L->absorbed) {
            for (L->i = 0; L->i < L->lc; L->i++) { wordbuf_push(&L->out, L->c[L->pc + L->i]); FR_YIELD(k); }
            wordbuf_push(&L->out, DNF_SEP);
        }
        if (L->from_x) L->px += L->lc + 1; else L->py += L->lc + 1;
    }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}

/* ---------------- meet ---------------- */
typedef struct {
    const uint64_t *x, *y; size_t nx, ny;
    size_t px, py, i, j, ex, ey;
    uint64_t last, acc; bool contra;
    WordBuf u; bool created;
} MeetLoc;

static void meet_step(Cont *k, uint64_t v, DKind kind) {
    MeetLoc *L = FR_LOC(k, MeetLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    if (k->w[0] == k->w[1]) FR_FINISH(k, k->w[0]);
    L->x = rget(k->w[0], &L->nx); L->y = rget(k->w[1], &L->ny);
    if (L->nx == 0 || rec_one(L->y, L->ny)) FR_FINISH(k, k->w[0]);
    if (L->ny == 0 || rec_one(L->x, L->nx)) FR_FINISH(k, k->w[1]);
    L->acc = iv_zero();
    for (L->px = 0; L->px < L->nx; L->px = L->ex + 1) {
        for (L->py = 0; L->py < L->ny; L->py = L->ey + 1) {
            /* the union of the two clauses, one atom per step; a face clause
             * with both (i=0) and (i=1) is the false face and is dropped */
            wordbuf_init(&L->u); L->contra = false; L->last = DNF_SEP;
            L->i = L->px; L->j = L->py;
            for (;;) {
                uint64_t a = L->x[L->i], b = L->y[L->j], t;
                if (a == DNF_SEP && b == DNF_SEP) break;
                if (a == b) { t = a; L->i++; L->j++; }
                else if (a < b) { t = a; L->i++; }
                else { t = b; L->j++; }
                if (kind == DK_FC && L->last != DNF_SEP && (L->last & 1) == 0 && t == L->last + 1) L->contra = true;
                wordbuf_push(&L->u, t); L->last = t;
                FR_YIELD(k);
            }
            L->ex = L->i; L->ey = L->j;
            wordbuf_push(&L->u, DNF_SEP);
            if (L->contra) { while (wordbuf_drain_one(&L->u)) FR_YIELD(k); }
            else {
                FR_CALL(k, id, intern_sub(k, &M.keys, &L->u, &L->created));
                FR_AWAIT(k, L->acc, F_JOIN, L->acc, id);
            }
        }
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
static void ivmeet_step(Cont *k, uint64_t v) { meet_step(k, v, DK_IV); }
static void fcmeet_step(Cont *k, uint64_t v) { meet_step(k, v, DK_FC); }

/* ---------------- negation (De Morgan) and endpoint faces ----------------
 * ¬(∨_c ∧_a a) = ∧_c ∨_a ¬a; the singletons of a clause's negated atoms, in
 * atom order, are a canonical DNF (a clause holding i and ¬i keeps both).
 * (r=1) = ∨_c ∧_a (a=1): a clause's literals are its atoms with the sign bit
 * flipped (a clause with i and ¬i is false); (r=0) = ∧_c ∨_a (a=0): the
 * literal (a=0) is the atom's own word. */
typedef struct { const uint64_t *x; size_t nx, px, i; uint64_t acc; bool contra; WordBuf u; bool created; } NegLoc;

static void ivneg_step(Cont *k, uint64_t v) {
    NegLoc *L = FR_LOC(k, NegLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->x = rget(k->w[0], &L->nx);
    if (L->nx == 0) FR_FINISH(k, iv_one());
    L->acc = iv_one();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        wordbuf_init(&L->u);
        for (L->i = L->px; L->x[L->i] != DNF_SEP; ) {
            uint64_t a = L->x[L->i];
            if ((a & 1) == 0 && L->x[L->i + 1] == a + 1) { wordbuf_push(&L->u, a); wordbuf_push(&L->u, DNF_SEP); wordbuf_push(&L->u, a + 1); wordbuf_push(&L->u, DNF_SEP); L->i += 2; }
            else { wordbuf_push(&L->u, a ^ 1); wordbuf_push(&L->u, DNF_SEP); L->i++; }
            FR_YIELD(k);
        }
        if (L->u.n == 0) FR_FINISH(k, iv_zero());          /* the clause 1: its complement is 0 */
        FR_CALL(k, id, intern_sub(k, &M.keys, &L->u, &L->created));
        FR_AWAIT(k, L->acc, F_IVMEET, L->acc, id);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

static void fcend_step(Cont *k, uint64_t v) {
    NegLoc *L = FR_LOC(k, NegLoc);
    uint64_t id = 0;
    int eps = (int)k->w[1];
    FR_BEGIN(k);
    L->x = rget(k->w[0], &L->nx);
    L->acc = eps ? iv_zero() : iv_one();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        wordbuf_init(&L->u); L->contra = false;
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            uint64_t a = L->x[L->i];
            if (eps) {
                if ((a & 1) == 0 && L->x[L->i + 1] == a + 1) L->contra = true;
                wordbuf_push(&L->u, a ^ 1);
            } else { wordbuf_push(&L->u, a); wordbuf_push(&L->u, DNF_SEP); }
            FR_YIELD(k);
        }
        if (eps) {
            wordbuf_push(&L->u, DNF_SEP);
            if (L->contra) { while (wordbuf_drain_one(&L->u)) FR_YIELD(k); continue; }
            FR_CALL(k, id, intern_sub(k, &M.keys, &L->u, &L->created));
            FR_AWAIT(k, L->acc, F_JOIN, L->acc, id);
        } else {
            if (L->u.n == 0) FR_FINISH(k, iv_zero());     /* (1 = 0) is false */
            FR_CALL(k, id, intern_sub(k, &M.keys, &L->u, &L->created));
            FR_AWAIT(k, L->acc, F_FCMEET, L->acc, id);
        }
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- entailment: every clause of χ contains a clause of φ ---------------- */
typedef struct { const uint64_t *x, *y; size_t nx, ny, px, py, i, j; bool found; } EntLoc;
static void fcent_step(Cont *k, uint64_t v) {
    EntLoc *L = FR_LOC(k, EntLoc);
    FR_BEGIN(k);
    if (k->w[0] == k->w[1]) FR_FINISH(k, 2);
    L->x = rget(k->w[0], &L->nx); L->y = rget(k->w[1], &L->ny);
    if (L->nx == 0 || rec_one(L->y, L->ny)) FR_FINISH(k, 2);
    if (L->ny == 0) FR_FINISH(k, 1);
    for (L->px = 0; L->px < L->nx; ) {
        L->found = false;
        for (L->py = 0; L->py < L->ny && !L->found; ) {
            L->i = L->px; L->j = L->py;
            for (;;) {
                uint64_t a = L->x[L->i], b = L->y[L->j];
                if (b == DNF_SEP) { L->found = true; break; }
                if (a == b) { L->i++; L->j++; }
                else if (a != DNF_SEP && a < b) L->i++;
                else { while (L->y[L->j] != DNF_SEP) { L->j++; FR_YIELD(k); } L->py = L->j + 1; break; }
                FR_YIELD(k);
            }
        }
        if (!L->found) FR_FINISH(k, 1);
        while (L->x[L->px] != DNF_SEP) { L->px++; FR_YIELD(k); }
        L->px++;
    }
    FR_FINISH(k, 2);
    FR_END(k);
}

/* ---------------- ∀i: the clauses without a literal on i (a canonical subsequence) ---------------- */
typedef struct { const uint64_t *x; size_t nx, px, i; bool mentions; WordBuf out; bool created; } AllLoc;
static void fcforall_step(Cont *k, uint64_t v) {
    AllLoc *L = FR_LOC(k, AllLoc);
    uint64_t id = 0;
    DimVarId dim = (DimVarId)k->w[1];
    FR_BEGIN(k);
    L->x = rget(k->w[0], &L->nx);
    wordbuf_init(&L->out);
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        L->mentions = false;
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) { if (FC_LIT_DIM(L->x[L->i]) == dim) L->mentions = true; FR_YIELD(k); }
        if (!L->mentions) {
            for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) { wordbuf_push(&L->out, L->x[L->i]); FR_YIELD(k); }
            wordbuf_push(&L->out, DNF_SEP);
        }
    }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}

/* ---------------- π_S: each clause restricted to S, joined ---------------- */
typedef struct { const uint64_t *x, *s; size_t nx, ns, px, i, lo, hi; uint64_t acc; WordBuf u; bool created, in; } ProjLoc;
static void fcproj_step(Cont *k, uint64_t v) {
    ProjLoc *L = FR_LOC(k, ProjLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->x = rget(k->w[0], &L->nx);
    if (L->nx == 0 || rec_one(L->x, L->nx)) FR_FINISH(k, k->w[0]);
    L->s = rget(k->w[1], &L->ns);
    L->acc = iv_zero();
    for (L->px = 0; L->px < L->nx; L->px = L->i + 1) {
        wordbuf_init(&L->u);
        for (L->i = L->px; L->x[L->i] != DNF_SEP; L->i++) {
            /* membership of the literal's dimension in S: one probe per step */
            L->lo = 0; L->hi = L->ns; L->in = false;
            while (L->lo < L->hi) {
                size_t mid = (L->lo + L->hi) / 2; uint64_t d = FC_LIT_DIM(L->x[L->i]);
                if (L->s[mid] == d) { L->in = true; break; }
                if (L->s[mid] < d) L->lo = mid + 1; else L->hi = mid;
                FR_YIELD(k);
            }
            if (L->in) wordbuf_push(&L->u, L->x[L->i]);
            FR_YIELD(k);
        }
        if (L->u.n == 0) FR_FINISH(k, iv_one());     /* a clause projects to ⊤ */
        wordbuf_push(&L->u, DNF_SEP);
        FR_CALL(k, id, intern_sub(k, &M.keys, &L->u, &L->created));
        FR_AWAIT(k, L->acc, F_JOIN, L->acc, id);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- sorted sets ---------------- */
typedef struct { const uint64_t *x, *y; size_t nx, ny, i, j, lo, hi, at; WordBuf out; bool created; } SetLoc;
static void union_step(Cont *k, uint64_t v) {
    SetLoc *L = FR_LOC(k, SetLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    if (k->w[0] == k->w[1]) FR_FINISH(k, k->w[0]);
    L->x = set_get(k->w[0], &L->nx); L->y = set_get(k->w[1], &L->ny);
    if (L->nx == 0) FR_FINISH(k, k->w[1]);
    if (L->ny == 0) FR_FINISH(k, k->w[0]);
    wordbuf_init(&L->out);
    for (L->i = L->j = 0; L->i < L->nx || L->j < L->ny; ) {
        if (L->j == L->ny || (L->i < L->nx && L->x[L->i] < L->y[L->j])) wordbuf_push(&L->out, L->x[L->i++]);
        else if (L->i == L->nx || L->y[L->j] < L->x[L->i]) wordbuf_push(&L->out, L->y[L->j++]);
        else { wordbuf_push(&L->out, L->x[L->i]); L->i++; L->j++; }
        FR_YIELD(k);
    }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}
/* binary search of w[1] in w[0], one probe per step; then (remove) the copy */
static void member_step(Cont *k, uint64_t v, bool remove) {
    SetLoc *L = FR_LOC(k, SetLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    L->x = set_get(k->w[0], &L->nx);
    L->lo = 0; L->hi = L->nx;
    while (!sorted_probe(L->x, 1, k->w[1], &L->lo, &L->hi, &L->at)) FR_YIELD(k);
    if (!remove) FR_FINISH(k, L->at ? 2 : 1);
    if (!L->at) FR_FINISH(k, k->w[0]);
    wordbuf_init(&L->out);
    for (L->i = 0; L->i < L->nx; L->i++) { if (L->x[L->i] != k->w[1]) wordbuf_push(&L->out, L->x[L->i]); FR_YIELD(k); }
    FR_CALL(k, id, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, id);
    FR_END(k);
}
static void remove_step(Cont *k, uint64_t v) { member_step(k, v, true); }
static void contains_step(Cont *k, uint64_t v) { member_step(k, v, false); }

void dnf_families_init(void) {
    family_define(F_JOIN, "dnf.join", join_step, sizeof(JoinLoc));
    family_define(F_IVMEET, "iv.meet", ivmeet_step, sizeof(MeetLoc));
    family_define(F_FCMEET, "fc.meet", fcmeet_step, sizeof(MeetLoc));
    family_define(F_IVNEG, "iv.negate", ivneg_step, sizeof(NegLoc));
    family_define(F_FCEND, "fc.endpoint", fcend_step, sizeof(NegLoc));
    family_define(F_FCENT, "fc.entails", fcent_step, sizeof(EntLoc));
    family_define(F_FCFORALL, "fc.forall", fcforall_step, sizeof(AllLoc));
    family_define(F_FCPROJ, "fc.project", fcproj_step, sizeof(ProjLoc));
    family_define(F_SUNION, "set.union", union_step, sizeof(SetLoc));
    family_define(F_SREMOVE, "set.remove", remove_step, sizeof(SetLoc));
    family_define(F_SCONTAINS, "set.contains", contains_step, sizeof(SetLoc));
}

/* ---------------- the operations (synchronous driver for callers that are
 * not yet frame programs; frame programs request the families) ---------------- */
IntervalId iv_join(IntervalId r, IntervalId s) { return family_call(F_JOIN, r, s); }
IntervalId iv_meet(IntervalId r, IntervalId s) { return family_call(F_IVMEET, r, s); }
IntervalId iv_negate(IntervalId r) { return family_call(F_IVNEG, r, 0); }
FaceId fc_join(FaceId a, FaceId b) { return family_call(F_JOIN, a, b); }
FaceId fc_meet(FaceId a, FaceId b) { return family_call(F_FCMEET, a, b); }
FaceId fc_endpoint(IntervalId r, int eps) { return family_call(F_FCEND, r, eps ? 1 : 0); }
bool fc_entails(FaceId chi, FaceId phi) { return family_call(F_FCENT, chi, phi) == 2; }
FaceId fc_forall(DimVarId i, FaceId phi) { return family_call(F_FCFORALL, phi, i); }
FaceId fc_project(FaceId chi, DimSetId S) { return family_call(F_FCPROJ, chi, S); }
uint64_t set_union(uint64_t a, uint64_t b) { return family_call(F_SUNION, a, b); }
uint64_t set_remove(uint64_t a, uint64_t x) { return family_call(F_SREMOVE, a, x); }
bool set_contains(uint64_t a, uint64_t x) { return family_call(F_SCONTAINS, a, x) == 2; }
