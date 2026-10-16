/* White-box bounded-step probe; link production modules except work.o.
 * The first probe stages exactly the NORMALIZE frame used by family_make
 * and op_antichain. The second uses public support operation handles.
 */
#include "work.c"
#include <assert.h>

static int normalize_probe(size_t n) {
    Frame f=fr(OF_NORMALIZE,0,0,0,0);
    for(size_t k=0;k<n;k++) words_push(&f.buf,set_empty());
    OpId h=op_new(OF_NORMALIZE,PH_REWRITE,f);
    uint64_t before=work_total_frames();
    assert(op_step(h,1)==OP_RUNNING);
    Op *j=JOB(HND(h)->job);
    size_t written=top(j)->buf2.n;
    uint64_t charged=work_total_frames()-before;
    printf("normalize n=%zu budget=1 handle_frames=%llu ledger_frames=%llu flags_written=%zu\n",
           n,(unsigned long long)op_frames(h),(unsigned long long)charged,written);
    op_release(h);
    return written>CHUNK_WORDS;
}

static int fanout_probe(size_t n) {
    FormulaId base=formula_and(formula_atom(atom_named(1)),formula_atom(atom_named(2)));
    OpId child_handle=op_support(base);
    uint64_t child_job=HND(child_handle)->job;
    for(size_t k=0;k<n;k++) {
        FormulaId root=formula_and(base,formula_atom(atom_named(1000+k)));
        OpId parent=op_support(root);
        size_t steps=0;
        while(JOB(HND(parent)->job)->waiting_on!=child_job) {
            assert(op_step(parent,1)==OP_RUNNING);
            assert(++steps<1000);
        }
        op_release(parent); /* releasing a handle correctly leaves its job */
    }
    assert(JOB(child_job)->waiters.len==n);
    uint64_t max_deliveries=0;
    while(op_status(child_handle)==OP_RUNNING) {
        WorkLedger before=work_ledger();
        op_step(child_handle,1);
        WorkLedger after=work_ledger();
        uint64_t d=after.frames[FR_ALIAS_DELIVERY]-before.frames[FR_ALIAS_DELIVERY];
        if(d>max_deliveries) max_deliveries=d;
    }
    assert(op_status(child_handle)==OP_COMPLETE);
    printf("fanout parents=%zu budget=1 max_deliveries_in_one_step=%llu\n",n,(unsigned long long)max_deliveries);
    op_release(child_handle);
    return max_deliveries>CHUNK_WORDS;
}

int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    int bad=normalize_probe(64)+normalize_probe(4096)+fanout_probe(256);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    return bad?1:0;
}
