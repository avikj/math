/* A reading as a word for test arithmetic: out of range is a test failure,
 * never a wrapped value. */
#ifndef CUBICAL_TEST_READING_H
#define CUBICAL_TEST_READING_H
#include "../src/eval.h"
static inline uint64_t rd(Reading r, Family f) {
    Exact x = { 0, NULL }; uint64_t v;
    eval_reading(r, f, &x);
    if (!exact_to_u64(&x, &v)) { printf("reading out of the word range\n"); exit(2); }
    exact_free(&x);
    return v;
}
#endif
