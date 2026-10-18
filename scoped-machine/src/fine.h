/* fine.h — the fine work vector of the C kernel (§89.2).
 *
 * The coarse event vector (REQUEST / EVAL / PUB / DELIVER) is a semantic
 * diagnostic; it does not bound the C work by a size-independent constant
 * (§89.1: a system with 1, 64 or 1024 branches has the same coarse vector
 * while open_ref iterates 2, 128 or 2048 fields). These counters expose the
 * work the kernel's loops actually perform: one increment per field opened,
 * per key word hashed, per probe, per compared word, per copied word, per
 * relocated slot, per map entry visited, per DNF clause step, per waiter
 * delivered, per continuation registered, per queue operation, per lock
 * acquisition, per cell allocated or released, per checker frame and per
 * proof-audit step. They are counted where the loop runs and are reported
 * beside the coarse vector, never added to it.
 */
#ifndef CUBICAL_FINE_H
#define CUBICAL_FINE_H
#include <stdint.h>
#include <stddef.h>
#include "xcount.h"
#include "event.h"
#include "kframe.h"

typedef enum {
    FC_FIELDS_OPENED = 0,     /* open_ref / tview_open: one per stored field */
    FC_HEAD_CELLS,            /* head field arrays allocated */
    FC_REINDEX_CALLS,         /* reindex / make_view / compose calls */
    FC_MAP_ENTRIES,           /* map entries, boundary variables and dimensions visited while building or restricting maps */
    FC_INTERN_WORDS_HASHED,
    FC_INTERN_PROBES,
    FC_INTERN_WORD_COMPARES,
    FC_INTERN_WORDS_COPIED,
    FC_INTERN_SLOTS_RELOCATED,
    FC_DNF_CLAUSE_STEPS,      /* clauses / atoms examined by the DNF algorithms */
    FC_FACE_OPS,              /* face operations requested by the evaluator and checker (entails, meet, join, project, reindex) */
    FC_WAITERS_DELIVERED,
    FC_CONTS_REGISTERED,
    FC_QUEUE_OPS,             /* enqueue / dequeue of evaluator jobs and net pairs */
    FC_LOCK_ATTEMPTS,         /* mutex acquisitions in the evaluator and net */
    FC_CELLS_ALLOCATED,       /* continuations, results, joins, entries, net nodes */
    FC_CELLS_RELEASED,
    FC_NET_ACTIONS,           /* committed net replacements */
    FC_NET_RETRIES,
    FC_CHECK_FRAMES,          /* checker budget steps */
    FC_AUDIT_STEPS,           /* proof-use audit traversal steps */
    FC_SHAPE_NODES,           /* shape nodes constructed (shape_of) */
    FC_VALIDATE_STEPS,        /* structural validation: nodes, fields and locals visited */
    FC_ALLOC_OPS,             /* kalloc: slots taken or returned */
    FC_ALLOC_WORDS,           /* kalloc: words cleared (calloc) or copied (realloc), one transition each */
    FC_SORT_STEPS,            /* sort_unique_u64: one sift (≤ 64 iterations) or one dedupe step */
    FC_ADAPTER_STEPS,         /* find_adapter: one candidate position examined under entries_mu */
    FC_COPY_WORDS,            /* words_append / variable-length copies: one word per transition */
    FC_CLAIM_STEPS,           /* checker claim resolution: one claim or one premise examined under K.mu */
    FC_NAT_LIMBS,             /* exact naturals: one limb read, produced or compared */
    FC_CHAIN_STEPS,           /* chain readings: one unit of BOUNDARY / PAIR / MAP_CHAIN / cochain value / law instance / admission check */
    FC_COUNT
} FineCounter;

/* V23 R5: each counter is an exact natural (xcount.h); fine_count and
 * FineVector are checked word projections (fatal when a count no longer fits
 * a word), fine_snap / fine_exact the authoritative exact readings */
extern XCount fine_counters[FC_COUNT];
/* §94: a fine step is a transition of the running frame stack (kframe.h) */
extern __thread uint64_t fine_tl_steps;   /* this thread's fine steps (the lock-section audit) */
static inline void fine_bump(FineCounter c) { xc_add(&fine_counters[c], 1); ev_add((unsigned)c, 1); fine_tl_steps++; kf_tick((int)c); }
static inline void fine_add(FineCounter c, uint64_t n) { xc_add(&fine_counters[c], n); ev_add((unsigned)c, n); fine_tl_steps += n; kf_tickn((int)c, n); }
uint64_t fine_count(FineCounter c);            /* checked word projection */
XSnap fine_snap(FineCounter c);                /* exact snapshot */
uint64_t xs_nat(XSnap s);                      /* an exact snapshot as a Nat (nat.h) */
uint64_t fine_exact(FineCounter c);            /* the exact reading as a Nat (nat.h; needs a live machine for boxed values) */
void fine_seed(FineCounter c, uint64_t low);   /* tests: a valid boundary state */
const char *fine_name(FineCounter c);
void fine_reset(void);          /* machine teardown only */
typedef struct { uint64_t v[FC_COUNT]; } FineVector;
FineVector fine_snapshot(void);
FineVector fine_delta(FineVector before, FineVector after);
#endif
