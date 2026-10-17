#include "common.h"
#include "fine.h"
#include "nat.h"
XCount fine_counters[FC_COUNT];
__thread uint64_t fine_tl_steps;
#define counters fine_counters
static const char *names[FC_COUNT] = { "fields_opened", "head_cells", "reindex_calls", "map_entries", "intern_words_hashed", "intern_probes", "intern_word_compares", "intern_words_copied", "intern_slots_relocated", "dnf_clause_steps", "face_ops", "waiters_delivered", "conts_registered", "queue_ops", "lock_attempts", "cells_allocated", "cells_released", "net_actions", "net_retries", "check_frames", "audit_steps", "shape_nodes", "validate_steps", "alloc_ops", "alloc_words", "sort_steps", "adapter_steps", "copy_words", "claim_steps", "nat_limbs" };
uint64_t fine_count(FineCounter c) { return xs_u64_checked(xc_snap(&counters[c]), names[c]); }
XSnap fine_snap(FineCounter c) { return xc_snap(&counters[c]); }
void fine_seed(FineCounter c, uint64_t low) { xc_seed(&counters[c], low); }
/* exact reading: low + 2^64 · carries, the carry count folded one record per step */
Nat xs_nat(XSnap s) {
    Nat k = 0;
    for (const XCarry *r = s.carry; r; r = r->next) k = nat_successor(k);
    if (!k) return nat_from_word(s.low);
    size_t n; uint64_t t; const uint64_t *kl = nat_limbs(k, &n, &t);
    uint64_t *w = (malloc)((n + 1) * sizeof(uint64_t)); w[0] = s.low; for (size_t i = 0; i < n; i++) w[i + 1] = kl[i];
    Nat v = nat_from_limbs(n + 1, w); (free)(w); return v;
}
uint64_t fine_exact(FineCounter c) { return xs_nat(fine_snap(c)); }
const char *fine_name(FineCounter c) { return names[c]; }
void fine_reset(void) { for (int i = 0; i < FC_COUNT; i++) xc_reset(&counters[i]); }
FineVector fine_snapshot(void) { FineVector f; for (int i = 0; i < FC_COUNT; i++) f.v[i] = fine_count((FineCounter)i); return f; }
FineVector fine_delta(FineVector b, FineVector a) { FineVector d; for (int i = 0; i < FC_COUNT; i++) { require(a.v[i] >= b.v[i], "fine_delta: snapshots out of order"); d.v[i] = a.v[i] - b.v[i]; } return d; }

void kernel_sort_step(void) { fine_bump(FC_SORT_STEPS); }
