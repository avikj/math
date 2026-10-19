#include "face.h"

/* the constants: canonical by construction */
FaceId fc_false(void) { return interner_intern(&M.faces, NULL, 0, NULL); }
FaceId fc_true(void) { uint64_t w[1] = { DNF_SEP }; return interner_intern(&M.faces, w, 1, NULL); }
FaceId fc_lit(DimVarId i, int eps) { uint64_t w[2] = { FC_LIT(i, eps), DNF_SEP }; return interner_intern(&M.faces, w, 2, NULL); }
bool fc_is_false(FaceId a) { size_t n; (void)interner_get(&M.faces, a, &n); return n == 0; }
bool fc_is_true(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); return n == 1 && w[0] == DNF_SEP; }

static void fc_lit_print(uint64_t l, FILE *f) { fprintf(f, "(d%llu=%d)", (unsigned long long)FC_LIT_DIM(l), FC_LIT_EPS(l)); }
void fc_print(FaceId a, FILE *f) { size_t n; const uint64_t *w = interner_get(&M.faces, a, &n); dnf_print(w, n, f, "⊥", "⊤", fc_lit_print); }

/* ---- sets ---- */
static uint64_t set_make(Interner *t, uint64_t *elems, size_t n) {
    n = sort_unique_u64(elems, n);
    return interner_intern(t, elems, n, NULL);
}
DimSetId dimset_make(uint64_t *e, size_t n) { return set_make(&M.dimsets, e, n); }
const uint64_t *dimset_get(DimSetId s, size_t *n) { return interner_get(&M.dimsets, s, n); }
VarSetId varset_make(uint64_t *e, size_t n) { return set_make(&M.varsets, e, n); }
const uint64_t *varset_get(VarSetId s, size_t *n) { return interner_get(&M.varsets, s, n); }

