#include "fine.h"
uint64_t fine_counters[FC_COUNT];
__thread uint64_t fine_tl_steps;
#define counters fine_counters
static const char *names[FC_COUNT] = { "fields_opened", "head_cells", "reindex_calls", "map_entries", "intern_words_hashed", "intern_probes", "intern_word_compares", "intern_words_copied", "intern_slots_relocated", "dnf_clause_steps", "face_ops", "waiters_delivered", "conts_registered", "queue_ops", "lock_attempts", "cells_allocated", "cells_released", "net_actions", "net_retries", "check_frames", "audit_steps", "shape_nodes", "validate_steps", "alloc_ops", "alloc_words", "sort_steps", "adapter_steps", "copy_words", "claim_steps", "nat_limbs" };
uint64_t fine_count(FineCounter c) { return __atomic_load_n(&counters[c], __ATOMIC_SEQ_CST); }
const char *fine_name(FineCounter c) { return names[c]; }
void fine_reset(void) { for (int i = 0; i < FC_COUNT; i++) __atomic_store_n(&counters[i], 0, __ATOMIC_SEQ_CST); }
FineVector fine_snapshot(void) { FineVector f; for (int i = 0; i < FC_COUNT; i++) f.v[i] = fine_count((FineCounter)i); return f; }
FineVector fine_delta(FineVector b, FineVector a) { FineVector d; for (int i = 0; i < FC_COUNT; i++) d.v[i] = a.v[i] - b.v[i]; return d; }

void kernel_sort_step(void) { fine_bump(FC_SORT_STEPS); }
