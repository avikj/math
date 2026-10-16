#include "work.c"
#include <assert.h>
#include <string.h>

static int interleave(bool same) {
    AtomId a=atom_named(10001),b=atom_named(10002);
    FormulaId fa=formula_atom(a),fb=formula_atom(b);
    OpId ha=op_support(fa),hb=same?op_must(fa):op_support(fb);
    if(same)b=a;
    unsigned steps=0;
    while(op_status(ha)==OP_RUNNING || op_status(hb)==OP_RUNNING) {
        if(op_status(ha)==OP_RUNNING)op_step(ha,1);
        if(op_status(hb)==OP_RUNNING)op_step(hb,1);
        assert(++steps<10000);
    }
    assert(op_status(ha)==OP_COMPLETE && op_status(hb)==OP_COMPLETE);
    size_t na,nb; const uint64_t *wa=rec_words(op_result(ha),&na),*wb=rec_words(op_result(hb),&nb);
    bool ok=na==2 && nb==2 && wa[0]==K_SET && wb[0]==K_SET && wa[1]==a && wb[1]==b && (!same || op_result(ha)==op_result(hb));
    printf("alternating public op_support: a=%llu b=%llu; records=(%llu,%llu),(%llu,%llu); correct=%d\n",
        (unsigned long long)a,(unsigned long long)b,(unsigned long long)wa[0],(unsigned long long)wa[1],
        (unsigned long long)wb[0],(unsigned long long)wb[1],ok);
    op_release(ha);op_release(hb);return !ok;
}
static int growth(void) {
    AtomId a=atom_named(10001); FormulaId f=formula_atom(a);OpId h=op_support(f);
    unsigned steps=0;
    for(;;) {
        Op *tip=tip_of(JOB(HND(h)->job));Frame *t=top(tip);
        if(t->fam==OF_INTERN && t->ph==3 && t->i==t->buf.n)break;
        assert(op_step(h,1)==OP_RUNNING);assert(++steps<10000);
    }
    size_t old=W.tab.nslots;
    for(unsigned i=0;i<3000;i++)atom_named(30000+i);
    assert(W.tab.nslots>old);
    while(op_status(h)==OP_RUNNING)op_step(h,1);
    SetId got=op_result(h),expected=set_make(1,&a);
    printf("growth before publication: slots %zu -> %zu; framed_set=%llu canonical_set=%llu equal=%d\n",old,W.tab.nslots,(unsigned long long)got,(unsigned long long)expected,got==expected);
    op_release(h);return got!=expected;
}
static int drain(void) {
    for(size_t i=0;i<2000;i++)atom_named(20000+i);
    ModelId m=model_make(1,(KindWeights){1,1,1,1,1,1,1,1},set_empty());
    OpId h=op_reduce(formula_one(),m);
    assert(op_step(h,1)==OP_RUNNING);
    assert(top(JOB(HND(h)->job))->ph==1);
    ktab_begin_grow(); size_t n=W.tab.old_n; assert(W.tab.cursor==0);
    uint64_t before=op_frames(h);op_step(h,1);
    size_t advanced=W.tab.cursor;bool pending=W.tab.old!=NULL;
    printf("one reduction unit: charged_units=%llu old_slots=%zu cursor=%zu relocation_pending=%d (expected cursor<=32)\n",
        (unsigned long long)(op_frames(h)-before),n,advanced,pending);
    op_release(h);return advanced>CHUNK_WORDS;
}
int main(int argc,char **argv) {
    assert(argc==2);machine_init();eval_init();check_init();compiler_init();work_init();
    int bad=!strcmp(argv[1],"interleave")?interleave(false):!strcmp(argv[1],"same-key")?interleave(true):!strcmp(argv[1],"growth")?growth():drain();
    work_free();compiler_free();check_free();eval_free();machine_free();return bad;
}
