#ifndef CUBICAL_REUSE_H
#define CUBICAL_REUSE_H
#include "common.h"
#include "reuse_stats.h"
void reuse_bump(ReuseCounter c);
void reuse_reset_all(void);    /* machine teardown only */
#endif
