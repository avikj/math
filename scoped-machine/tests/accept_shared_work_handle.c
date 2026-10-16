#include "../src/work.h"
#include "reuse_stats.h"
#include <assert.h>
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    FormulaId f=formula_one();
    for(uint64_t i=1;i<=12;i++) f=formula_and(f,formula_atom(atom_named(i)));
    ModelId m=model_make(1,(KindWeights){.named=1},set_empty());
    OpId h1=op_reduce(f,m), h2=op_reduce(f,m);
    (void)op_step(h1,1);
    op_release(h1);
    while(op_step(h2,1)==OP_RUNNING) {}
    assert(op_status(h2)==OP_COMPLETE);
    uint64_t result=op_result(h2); op_release(h2);
    uint64_t count=reuse_count(REUSE_REDUCE_BODY);
    assert(count > 0);
    OpId h3=op_reduce(f,m);
    while(op_step(h3,1)==OP_RUNNING) {}
    assert(op_status(h3)==OP_COMPLETE && op_result(h3)==result);
    assert(reuse_count(REUSE_REDUCE_BODY)==count);
    op_release(h3);
    puts("PASS release of one consumer preserves another; completed reduction persists");
    work_free(); compiler_free(); check_free(); eval_free(); machine_free(); return 0;
}
