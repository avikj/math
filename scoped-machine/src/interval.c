#include "interval.h"

/* the constants: canonical by construction */
IntervalId iv_zero(void) { return interner_intern(&M.keys, NULL, 0, NULL); }
IntervalId iv_one(void) { uint64_t w[1] = { DNF_SEP }; return interner_intern(&M.keys, w, 1, NULL); }
IntervalId iv_var(DimVarId i) { uint64_t w[2] = { IV_ATOM(i, 0), DNF_SEP }; return interner_intern(&M.keys, w, 2, NULL); }
bool iv_is_zero(IntervalId r) { size_t n; (void)interner_get(&M.keys, r, &n); return n == 0; }
bool iv_is_one(IntervalId r) { size_t n; const uint64_t *w = interner_get(&M.keys, r, &n); return n == 1 && w[0] == DNF_SEP; }

void dnf_print(const uint64_t *w, size_t n, FILE *f, const char *zero, const char *one, void (*atom)(uint64_t a, FILE *f)) {
    if (n == 0) { fprintf(f, "%s", zero); return; }
    bool first_clause = true, first_atom = true;
    for (size_t p = 0; p < n; p++) {
        if (first_atom) { if (!first_clause) fprintf(f, " ∨ "); if (w[p] == DNF_SEP) fprintf(f, "%s", one); }
        if (w[p] == DNF_SEP) { first_clause = false; first_atom = true; continue; }
        if (!first_atom) fprintf(f, "∧");
        atom(w[p], f); first_atom = false;
    }
}
static void iv_atom_print(uint64_t a, FILE *f) { fprintf(f, "%sd%llu", IV_ATOM_NEG(a) ? "¬" : "", (unsigned long long)IV_ATOM_DIM(a)); }
void iv_print(IntervalId r, FILE *f) { size_t n; const uint64_t *w = interner_get(&M.keys, r, &n); dnf_print(w, n, f, "0", "1", iv_atom_print); }
