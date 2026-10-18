/* event.h — the primitive execution stream (HANDOFF §§6–7).
 *
 * Every bounded unit the machine executes (an evaluator task, a net pair
 * replacement, an engine unit, a kernel-continuation grant, an effect job, a
 * chain step) is one primitive event: an immutable record with its kind, its
 * one accounting owner, its occurrence identity, its causal predecessor and
 * its exact label — the transitions it took, per dimension. The dimensions
 * are the fine transition kinds and every registered counter family (the
 * semantic markers: reuse counters, evaluator / cut / effect events, ledger
 * frames). A macro marker is a label entry on the unit where its transition
 * happens; it is never added again by its children (labels are exclusive:
 * a nested unit's transitions belong to the nested unit).
 *
 * Records are appended to per-thread streams (single writer, published with
 * release; readers acquire the published length). Work done on a thread
 * outside any unit accumulates in its ambient label and is published as an
 * ambient record at the thread's next quiescent point (a worker before it
 * waits, a continuation before it yields, a client at ev_quiesce). The
 * record write is part of the bounded primitive it describes; it creates no
 * event of its own.
 *
 * Counters are projections of the stream: ev_fold_dims over a prefix gives
 * every dimension's exact total; the old counters remain shadows, and
 * ev_shadow_check compares every registered family with its fold at a
 * common quiescent prefix. */
#ifndef CUBICAL_EVENT_H
#define CUBICAL_EVENT_H
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "xcount.h"

#define ED_MAX 1024                     /* dimension slots (families register at init) */
#define ED_REUSE 31                     /* base of the reuse markers (fine transitions occupy 0..FC_COUNT-1) */
typedef enum { EK_AMBIENT = 0, EK_EVAL_TASK, EK_NET_PAIR, EK_ENGINE_UNIT, EK_KERNEL_GRANT, EK_EFFECT_JOB, EK_CHAIN_STEP, EK_COUNT } EvKind;
/* service owners (an event outside any client accounting scope) */
enum { EO_AMBIENT = 1, EO_EVAL, EO_NET, EO_ENGINE, EO_KERNEL, EO_EFFECT, EO_CHAIN, EO_SERVICE_COUNT };

extern __thread uint64_t ev_cur[ED_MAX];
extern __thread uint64_t ev_touch[ED_MAX / 64];
static inline void ev_add(unsigned d, uint64_t n) {
    uint64_t v = ev_cur[d]; ev_cur[d] = v + n;
    if (!v) ev_touch[d >> 6] |= (uint64_t)1 << (d & 63);
}

/* dimensions: fine transitions first, then the registered families */
unsigned ev_family(const char *name, unsigned n, XCount *shadow);   /* returns the base dimension; idempotent by name */
unsigned ev_family_base(const char *name);
unsigned ev_dims(void);
const char *ev_dim_name(unsigned d, unsigned *index);

void ev_init(void);                     /* machine_init */
void ev_free(void);                     /* machine_free (after every subsystem) */
bool ev_live(void);

/* units */
typedef struct { uint32_t stream; uint64_t index; } EvRef;
void ev_begin(EvKind kind, uint64_t occ, uint64_t cause);
EvRef ev_end(void);                     /* publishes the record; returns its reference */
void ev_owner_switch(void);             /* the accounting owner is about to change: the segment so far is published under the old owner */
void ev_owner_refresh(void);            /* after the change: the open unit continues under the new owner */
void ev_quiesce(void);                  /* publish this thread's ambient label */
size_t ev_depth(void);                  /* open units on this thread */
void ev_unwind_to(size_t depth);        /* a cancellation unwound past open units: each is published with the work it performed */
uint64_t ev_owner_current(EvKind kind); /* the owner a unit begun now would have */

/* prefixes and folds */
typedef struct { size_t n; struct EvStream **s; uint64_t *len; } EvPrefix;
EvPrefix ev_prefix(void);               /* every stream's published length, captured now */
void ev_prefix_free(EvPrefix *p);
/* occurrence namespaces: a record's occurrence identity is (namespace, id) */
enum { OCC_ENTRY = 1, OCC_NODE, OCC_OP, OCC_KJOB, OCC_EFFECT, OCC_CHAIN };
#define OCC(ns, id) (((uint64_t)(ns) << 56) | ((uint64_t)(id) & (((uint64_t)1 << 56) - 1)))
typedef struct { uint64_t owner; int kind; uint64_t occ; const uint64_t *occs; size_t nocc; } EvFilter;   /* 0 / -1 / 0 / NULL: any; occs: a sorted set of occurrence identities */
void ev_fold_dims(const EvPrefix *p, const EvFilter *f, XCount *out);   /* out[ED_MAX]: exact per-dimension totals */
uint64_t ev_count_records(const EvPrefix *p, const EvFilter *f);
/* HANDOFF §7: historical work of a support set. W(support) is the fold of the records whose occurrence is in the
 * set; the set is a union of realizations, so a shared producer's records are counted once (χ(A∪B) = χ(A)+χ(B)−χ(A∩B)) */
size_t ev_occ_union(const uint64_t *a, size_t na, const uint64_t *b, size_t nb, uint64_t **out);
size_t ev_occ_intersection(const uint64_t *a, size_t na, const uint64_t *b, size_t nb, uint64_t **out);
void ev_occ_sort(uint64_t *v, size_t *n);   /* sort and deduplicate in place */
/* HANDOFF §8: incremental work from an available history H0 is W(support(P) \ support(H0)) */
size_t ev_occ_difference(const uint64_t *a, size_t na, const uint64_t *b, size_t nb, uint64_t **out);
/* shadow comparison of every registered family at a quiescent prefix: returns
 * the number of mismatching dimensions (reports each on stderr when verbose) */
size_t ev_shadow_check(const EvPrefix *p, bool verbose);

typedef struct { uint64_t records, words, streams, segments, ambient; } EvStats;
EvStats ev_stats(void);
#endif
