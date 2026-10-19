/* count.h — exact counts (CONTINUATION-AND-COUNT-CLOSURE §C).
 *
 * A count is a word-sized low digit and a persistent sequence of carry
 * blocks,  value(l, B) = l + 2^64 · length(B).  One writer updates it in
 * bounded work: an increment that does not overflow changes l; an overflow
 * installs one carry block and resets l. A reader takes a consistent
 * snapshot (the low digit with its carry prefix) and adds it exactly into a
 * natural number of 64-bit limbs; a word conversion reports out-of-range
 * rather than wrapping.
 */
#ifndef CUBICAL_COUNT_H
#define CUBICAL_COUNT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct Carry { struct Carry *next; } Carry;
typedef struct { uint64_t low; Carry *carry; uint64_t seq; } Count;

void count_bump(Count *c);                       /* the single writer: one event */
void count_free(Count *c);                       /* no writer or reader remains */

typedef struct { size_t n; uint64_t *w; } Exact; /* little-endian limbs; n = 0 is zero */
void exact_add_count(Exact *x, const Count *c);  /* x += a snapshot of c */
void exact_add_word(Exact *x, size_t at, uint64_t v);   /* x += v · 2^(64·at) */
bool exact_to_u64(const Exact *x, uint64_t *out);
void exact_free(Exact *x);

#endif
