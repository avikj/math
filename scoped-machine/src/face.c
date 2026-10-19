#include "face.h"

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
bool fc_is_false(FaceId a) { size_t n; (void)interner_get(&M.faces, a, &n); return n == 0; }
bool fc_is_true(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); return n == 1 && w[0] == DNF_SEP; }


void fc_dims(FaceId phi, Words *out) {
    size_t n; const uint64_t *w = interner_get(&M.faces, phi, &n);
    for (size_t p = 0; p < n; p++) if (w[p] != DNF_SEP) words_push(out, FC_LIT_DIM(w[p]));
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
DimSetId dimset_make(uint64_t *e, size_t n) { return set_make(&M.dimsets, e, n); }
const uint64_t *dimset_get(DimSetId s, size_t *n) { return interner_get(&M.dimsets, s, n); }
VarSetId varset_make(uint64_t *e, size_t n) { return set_make(&M.varsets, e, n); }
const uint64_t *varset_get(VarSetId s, size_t *n) { return interner_get(&M.varsets, s, n); }

