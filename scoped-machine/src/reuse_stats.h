#ifndef SCOPED_MACHINE_REUSE_STATS_H
#define SCOPED_MACHINE_REUSE_STATS_H
#include <stdint.h>
/* ABI for the v9 acceptance tests. Counts actual semantic body/rule starts,
 * not requests or deliveries. Implement in the production machine; do not
 * supply a stub just to link these tests. Monotone within a machine lifetime. */
typedef enum {
    REUSE_EVAL_BODY = 0,
    REUSE_BETA,
    REUSE_FST,
    REUSE_SND,
    REUSE_PATH_BETA,
    REUSE_ENDPOINT,
    REUSE_GLOBAL_UNFOLD,
    REUSE_GLUE_RULE,
    REUSE_SYSTEM_RULE,
    REUSE_COMP_EXPAND,
    REUSE_IDENTITY_APPLY,
    REUSE_CONVERSION_BODY,
    REUSE_REDUCE_BODY,
    REUSE_PROOF_CHECK_BODY,
    REUSE_SHAPE_NODE,
    REUSE_DEPENDENCY_CHECK,
    REUSE_RECEIPT_INSTANCE,
    REUSE_READY_HIT,
    REUSE_RUNNING_JOIN,
    REUSE_COUNTER_COUNT
} ReuseCounter;
uint64_t reuse_count(ReuseCounter counter);
#endif
