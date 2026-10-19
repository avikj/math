#include "face.h"

/* the constants: canonical by construction */
FaceId fc_false(void) { return interner_intern(&M.keys, NULL, 0, NULL); }
FaceId fc_true(void) { uint64_t w[1] = { DNF_SEP }; return interner_intern(&M.keys, w, 1, NULL); }
FaceId fc_lit(DimVarId i, int eps) { uint64_t w[2] = { FC_LIT(i, eps), DNF_SEP }; return interner_intern(&M.keys, w, 2, NULL); }
bool fc_is_false(FaceId a) { size_t n; (void)interner_get(&M.keys, a, &n); return n == 0; }
bool fc_is_true(FaceId a) { size_t n; const uint64_t *w = interner_get(&M.keys, a, &n); return n == 1 && w[0] == DNF_SEP; }

static void fc_lit_print(uint64_t l, FILE *f) { fprintf(f, "(d%llu=%d)", (unsigned long long)FC_LIT_DIM(l), FC_LIT_EPS(l)); }
void fc_print(FaceId a, FILE *f) { size_t n; const uint64_t *w = interner_get(&M.keys, a, &n); dnf_print(w, n, f, "⊥", "⊤", fc_lit_print); }

/* ---- sets ---- */
uint64_t set_make(uint64_t *e, size_t n) { return interner_intern(&M.keys, e, sort_unique_u64(e, n), NULL); }
const uint64_t *set_get(uint64_t s, size_t *n) { return interner_get(&M.keys, s, n); }

