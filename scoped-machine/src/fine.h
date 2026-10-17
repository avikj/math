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
    FC_COUNT
} FineCounter;

extern uint64_t fine_counters[FC_COUNT];
/* §94: a fine step is the transition point of a kernel continuation (kcont.h) */
struct KCont; extern __thread struct KCont *kc_tl; extern __thread int kc_last_counter; void kc_tick(void);
extern __thread uint64_t fine_tl_steps;   /* this thread's fine steps (the lock-section audit) */
static inline void fine_bump(FineCounter c) { __atomic_add_fetch(&fine_counters[c], 1, __ATOMIC_RELAXED); fine_tl_steps++; if (kc_tl) { kc_last_counter = (int)c; kc_tick(); } }
static inline void fine_add(FineCounter c, uint64_t n) { __atomic_add_fetch(&fine_counters[c], n, __ATOMIC_RELAXED); fine_tl_steps += n; if (kc_tl) { kc_last_counter = (int)c; kc_tick(); } }
uint64_t fine_count(FineCounter c);
const char *fine_name(FineCounter c);
void fine_reset(void);          /* machine teardown only */
typedef struct { uint64_t v[FC_COUNT]; } FineVector;
FineVector fine_snapshot(void);
FineVector fine_delta(FineVector before, FineVector after);
#endif
