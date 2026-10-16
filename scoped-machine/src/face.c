#include "face.h"
#include "fine.h"

static bool face_contradiction(const Clause *c) {
    /* sorted: (i=0) = 2i and (i=1) = 2i+1 are adjacent when both present */
    for (size_t k = 0; k + 1 < c->n; k++)
        if ((c->a[k] & 1u) == 0 && c->a[k + 1] == c->a[k] + 1) return true;
    return false;
}

FaceId fc_from_dnf(Dnf *d) {
    dnf_normalize(d, face_contradiction);
    Words w; words_init(&w);
    dnf_encode(d, &w);
    FaceId id = interner_intern(&M.faces, w.w, w.n, NULL);
    words_free(&w);
    dnf_free(d);
    return id;
}

void fc_to_dnf(FaceId a, Dnf *d) {
    size_t n; const uint64_t *w = interner_get(&M.faces, a, &n);
    dnf_decode(d, w, n);
}

FaceId fc_false(void) { Dnf d; dnf_init(&d); return fc_from_dnf(&d); }
FaceId fc_true(void) { Dnf d; dnf_init(&d); dnf_add_clause(&d, NULL, 0); return fc_from_dnf(&d); }
FaceId fc_lit(DimVarId i, int eps) {
    Dnf d; dnf_init(&d);
    uint64_t l = FC_LIT(i, eps);
    dnf_add_clause(&d, &l, 1);
    return fc_from_dnf(&d);
}
bool fc_is_false(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); return w[0] == 0; }
bool fc_is_true(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); return w[0] == 1 && w[1] == 0; }

FaceId fc_join(FaceId a, FaceId b) {
    fine_bump(FC_FACE_OPS);
    Dnf x, y; fc_to_dnf(a, &x); fc_to_dnf(b, &y);
    for (size_t i = 0; i < y.n; i++) dnf_add_clause(&x, y.c[i].a, y.c[i].n);
    dnf_free(&y);
    return fc_from_dnf(&x);
}

FaceId fc_meet(FaceId a, FaceId b) {
    fine_bump(FC_FACE_OPS);
    Dnf x, y, out; fc_to_dnf(a, &x); fc_to_dnf(b, &y); dnf_init(&out);
    for (size_t i = 0; i < x.n; i++)
        for (size_t j = 0; j < y.n; j++)
            dnf_add_clause_union(&out, &x.c[i], &y.c[j]);
    dnf_free(&x); dnf_free(&y);
    return fc_from_dnf(&out);
}

static FaceId atom_endpoint(uint64_t atom, int eps) {
    /* (¬i = eps) = (i = 1-eps) */
    return fc_lit(IV_ATOM_DIM(atom), IV_ATOM_NEG(atom) ? 1 - eps : eps);
}

FaceId fc_endpoint(IntervalId r, int eps) {
    Dnf a; iv_to_dnf(r, &a);
    FaceId out;
    if (eps == 1) {
        /* (r=1) = OR over clauses of AND over atoms of (a=1) */
        out = fc_false();
        for (size_t i = 0; i < a.n; i++) {
            FaceId cl = fc_true();
            for (size_t k = 0; k < a.c[i].n; k++) cl = fc_meet(cl, atom_endpoint(a.c[i].a[k], 1));
            out = fc_join(out, cl);
        }
    } else {
        /* (r=0) = AND over clauses of OR over atoms of (a=0) */
        out = fc_true();
        for (size_t i = 0; i < a.n; i++) {
            FaceId cl = fc_false();
            for (size_t k = 0; k < a.c[i].n; k++) cl = fc_join(cl, atom_endpoint(a.c[i].a[k], 0));
            out = fc_meet(out, cl);
        }
    }
    dnf_free(&a);
    return out;
}

FaceId fc_substitute(FaceId phi, DimImageFn img, void *ctx) {
    Dnf a; fc_to_dnf(phi, &a);
    FaceId out = fc_false();
    for (size_t i = 0; i < a.n; i++) {
        FaceId cl = fc_true();
        for (size_t k = 0; k < a.c[i].n; k++) {
            uint64_t l = a.c[i].a[k];
            cl = fc_meet(cl, fc_endpoint(img(FC_LIT_DIM(l), ctx), FC_LIT_EPS(l)));
        }
        out = fc_join(out, cl);
    }
    dnf_free(&a);
    return out;
}

bool fc_entails(FaceId chi, FaceId phi) {
    fine_bump(FC_FACE_OPS);
    Dnf x, y; fc_to_dnf(chi, &x); fc_to_dnf(phi, &y);
    bool ok = true;
    for (size_t i = 0; i < x.n && ok; i++) {
        bool found = false;
        for (size_t j = 0; j < y.n && !found; j++) {
            fine_bump(FC_DNF_CLAUSE_STEPS);
            if (clause_subset(&y.c[j], &x.c[i])) found = true;
        }
        ok = found;
    }
    dnf_free(&x); dnf_free(&y);
    return ok;
}

FaceId fc_forall(DimVarId i, FaceId phi) {
    fine_bump(FC_FACE_OPS);
    Dnf a, out; fc_to_dnf(phi, &a); dnf_init(&out);
    for (size_t c = 0; c < a.n; c++) {
        bool mentions = false;
        for (size_t k = 0; k < a.c[c].n; k++) if (FC_LIT_DIM(a.c[c].a[k]) == i) { mentions = true; break; }
        if (!mentions) dnf_add_clause(&out, a.c[c].a, a.c[c].n);
    }
    dnf_free(&a);
    return fc_from_dnf(&out);
}

static bool sorted_contains(const uint64_t *S, size_t n, uint64_t x) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (S[mid] == x) return true;
        if (S[mid] < x) lo = mid + 1; else hi = mid;
    }
    return false;
}

FaceId fc_project(FaceId chi, const uint64_t *S, size_t nS) {
    fine_bump(FC_FACE_OPS);
    /* chi is canonical: contradictory clauses are already gone */
    Dnf a, out; fc_to_dnf(chi, &a); dnf_init(&out);
    Words buf; words_init(&buf);
    for (size_t c = 0; c < a.n; c++) {
        buf.n = 0;
        for (size_t k = 0; k < a.c[c].n; k++)
            if (sorted_contains(S, nS, FC_LIT_DIM(a.c[c].a[k]))) words_push(&buf, a.c[c].a[k]);
        dnf_add_clause(&out, buf.w, buf.n);
    }
    words_free(&buf);
    dnf_free(&a);
    return fc_from_dnf(&out);
}

void fc_dims(FaceId phi, Words *out) {
    size_t n; const uint64_t *w = interner_get(&M.faces, phi, &n);
    size_t nc = (size_t)w[0], p = 1;
    for (size_t i = 0; i < nc; i++) {
        size_t len = (size_t)w[p++];
        for (size_t k = 0; k < len; k++) words_push(out, FC_LIT_DIM(w[p + k]));
        p += len;
    }
}

void fc_print(FaceId a, FILE *f) {
    Dnf d; fc_to_dnf(a, &d);
    if (d.n == 0) { fprintf(f, "⊥"); dnf_free(&d); return; }
    for (size_t i = 0; i < d.n; i++) {
        if (i) fprintf(f, " ∨ ");
        if (d.c[i].n == 0) { fprintf(f, "⊤"); continue; }
        for (size_t k = 0; k < d.c[i].n; k++) {
            if (k) fprintf(f, "∧");
            fprintf(f, "(d%llu=%d)", (unsigned long long)FC_LIT_DIM(d.c[i].a[k]), FC_LIT_EPS(d.c[i].a[k]));
        }
    }
    dnf_free(&d);
}

/* ---- sets ---- */
static uint64_t set_make(Interner *t, uint64_t *elems, size_t n) {
    n = sort_unique_u64(elems, n);
    return interner_intern(t, elems, n, NULL);
}
static uint64_t set_union(Interner *t, uint64_t a, uint64_t b) {
    if (a == b) return a;
    size_t na, nb;
    const uint64_t *x = interner_get(t, a, &na);
    const uint64_t *y = interner_get(t, b, &nb);
    if (na == 0) return b;
    if (nb == 0) return a;
    uint64_t *buf = malloc((na + nb) * sizeof(uint64_t));
    require(buf, "out of memory");
    memcpy(buf, x, na * sizeof(uint64_t));
    memcpy(buf + na, y, nb * sizeof(uint64_t));
    uint64_t id = set_make(t, buf, na + nb);
    free(buf);
    return id;
}
static uint64_t set_remove(Interner *t, uint64_t a, uint64_t v) {
    size_t n; const uint64_t *x = interner_get(t, a, &n);
    if (!sorted_contains(x, n, v)) return a;
    uint64_t *buf = malloc((n ? n : 1) * sizeof(uint64_t));
    require(buf, "out of memory");
    size_t m = 0;
    for (size_t i = 0; i < n; i++) if (x[i] != v) buf[m++] = x[i];
    uint64_t id = interner_intern(t, buf, m, NULL);
    free(buf);
    return id;
}
static bool set_contains(Interner *t, uint64_t a, uint64_t v) {
    size_t n; const uint64_t *x = interner_get(t, a, &n);
    return sorted_contains(x, n, v);
}

DimSetId dimset_make(uint64_t *e, size_t n) { return set_make(&M.dimsets, e, n); }
const uint64_t *dimset_get(DimSetId s, size_t *n) { return interner_get(&M.dimsets, s, n); }
DimSetId dimset_union(DimSetId a, DimSetId b) { return set_union(&M.dimsets, a, b); }
DimSetId dimset_remove(DimSetId a, uint64_t x) { return set_remove(&M.dimsets, a, x); }
bool dimset_contains(DimSetId a, uint64_t x) { return set_contains(&M.dimsets, a, x); }
VarSetId varset_make(uint64_t *e, size_t n) { return set_make(&M.varsets, e, n); }
const uint64_t *varset_get(VarSetId s, size_t *n) { return interner_get(&M.varsets, s, n); }
VarSetId varset_union(VarSetId a, VarSetId b) { return set_union(&M.varsets, a, b); }
VarSetId varset_remove(VarSetId a, uint64_t x) { return set_remove(&M.varsets, a, x); }
bool varset_contains(VarSetId a, uint64_t x) { return set_contains(&M.varsets, a, x); }
