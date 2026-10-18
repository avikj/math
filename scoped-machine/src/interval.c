#include "interval.h"

IntervalId iv_from_dnf(Dnf *d) {
    dnf_normalize(d, NULL);
    Words w; words_init(&w);
    dnf_encode(d, &w);
    IntervalId id = interner_intern(&M.intervals, w.w, w.n, NULL);
    words_free(&w);
    dnf_free(d);
    return id;
}

void iv_to_dnf(IntervalId r, Dnf *d) {
    size_t n;
    const uint64_t *w = interner_get(&M.intervals, r, &n);
    dnf_decode(d, w, n);
}

IntervalId iv_zero(void) { Dnf d; dnf_init(&d); return iv_from_dnf(&d); }
IntervalId iv_one(void) { Dnf d; dnf_init(&d); dnf_add_clause(&d, NULL, 0); return iv_from_dnf(&d); }
IntervalId iv_var(DimVarId i) {
    Dnf d; dnf_init(&d);
    uint64_t a = IV_ATOM(i, 0);
    dnf_add_clause(&d, &a, 1);
    return iv_from_dnf(&d);
}
bool iv_is_zero(IntervalId r) { size_t n; (void)interner_get(&M.intervals, r, &n); return n == 0; }
bool iv_is_one(IntervalId r) { size_t n; const uint64_t *w = interner_get(&M.intervals, r, &n); return n == 1 && w[0] == DNF_SEP; }

IntervalId iv_substitute(IntervalId r, DimImageFn img, void *ctx) {
    /* Insert the image of each original dimension once (positive atom →
     * image, negative atom → negation of image), combine by the original
     * meets and joins. No recursion into inserted images. */
    Dnf a; iv_to_dnf(r, &a);
    IntervalId out = iv_zero();
    for (size_t i = 0; i < a.n; i++) {
        IntervalId cl = iv_one();
        for (size_t k = 0; k < a.c[i].n; k++) {
            uint64_t at = a.c[i].a[k];
            IntervalId im = img(IV_ATOM_DIM(at), ctx);
            if (IV_ATOM_NEG(at)) im = iv_negate(im);
            cl = iv_meet(cl, im);
        }
        out = iv_join(out, cl);
    }
    dnf_free(&a);
    return out;
}

void iv_dims(IntervalId r, Words *out) {
    size_t n; const uint64_t *w = interner_get(&M.intervals, r, &n);
    for (size_t p = 0; p < n; p++) if (w[p] != DNF_SEP) words_push(out, IV_ATOM_DIM(w[p]));
}

void iv_print(IntervalId r, FILE *f) {
    Dnf a; iv_to_dnf(r, &a);
    if (a.n == 0) { fprintf(f, "0"); dnf_free(&a); return; }
    for (size_t i = 0; i < a.n; i++) {
        if (i) fprintf(f, " ∨ ");
        if (a.c[i].n == 0) { fprintf(f, "1"); continue; }
        for (size_t k = 0; k < a.c[i].n; k++) {
            if (k) fprintf(f, "∧");
            uint64_t at = a.c[i].a[k];
            fprintf(f, "%sd%llu", IV_ATOM_NEG(at) ? "¬" : "", (unsigned long long)IV_ATOM_DIM(at));
        }
    }
    dnf_free(&a);
}
