/* Non-moving sparse pointer index over the entire size_t domain.
 * Fixed fanout bounds one directory operation, not the represented size.
 * Directory roots are partitioned by index width so existing roots never move.
 */
#ifndef CUBICAL_RADIX_H
#define CUBICAL_RADIX_H
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>
#define RADIX_BITS 9u
#define RADIX_FANOUT ((size_t)1 << RADIX_BITS)
#define RADIX_LEVELS ((sizeof(size_t) * CHAR_BIT + RADIX_BITS - 1) / RADIX_BITS)
typedef struct { void *root[RADIX_LEVELS]; } Radix;
void radix_init(Radix *r);
void **radix_slot(Radix *r, size_t index, bool create);
void *radix_get(const Radix *r, size_t index);
/* Quiescent retirement: one directory page per call, no payload release.
 * The fixed-depth cursor lives with the owner until retirement completes. */
typedef struct {
    Radix tree;
    void *stack[RADIX_LEVELS];
    size_t next[RADIX_LEVELS];
    size_t root, depth;
} RadixRetire;
void radix_retire_begin(RadixRetire *s, Radix *r);
bool radix_retire_step(RadixRetire *s);
typedef void (*RadixLeafFn)(void *value, void *ctx);
void radix_free(Radix *r, RadixLeafFn release, void *ctx);
#endif
