#include "work.c"
#include <assert.h>

static void stage(OpId h, unsigned phase) {
    size_t count = 0;
    while (top(JOB(HND(h)->job))->ph != phase) {
        assert(op_step(h, 1) == OP_RUNNING);
        assert(++count < 100000);
    }
}
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    uint64_t a[64], b[128]; a[0] = b[0] = K_LIST;
    for (size_t i=1; i<64; i++) a[i]=900000+i;
    for (size_t i=1; i<128; i++) b[i]=910000+i;
    OpId writer=op_new(OF_INTERN,PH_REWRITE,fr_intern(a,64));
    OpId grower=op_new(OF_INTERN,PH_REWRITE,fr_intern(b,128));
    OpId lookup=op_new(OF_LOOKUP,PH_REWRITE,fr_lookup(a,64));
    stage(writer,3);
    size_t off=top(JOB(HND(writer)->job))->acc2;
    for(size_t k=0; W.tab.store.cap<4096 || W.tab.store.cap-W.tab.store.n>8; k++) {
        uint64_t x[3]={K_LIST,920000,k}; intern_sync(x,3,NULL);
    }
    stage(grower,5);
    assert(op_step(grower,1)==OP_RUNNING && W.tab.sold && W.tab.smoved==0);
    while(W.tab.smoved<=off+2) assert(op_step(grower,1)==OP_RUNNING && W.tab.sold);
    size_t cursor=W.tab.smoved;
    assert(op_step(writer,1)==OP_RUNNING);
    assert(W.tab.sold[off+2]==a[0] && W.tab.store.w[off+2]==a[0]);
    while(op_status(writer)==OP_RUNNING) op_step(writer,1);
    assert(op_status(writer)==OP_COMPLETE && W.tab.sold && W.tab.smoved==cursor);
    uint64_t id=op_result(writer); size_t n; const uint64_t *w=rec_words(id,&n);
    assert(n==64); for(size_t i=0;i<n;i++) assert(w[i]==a[i]);
    while(op_status(lookup)==OP_RUNNING) op_step(lookup,1);
    assert(op_status(lookup)==OP_COMPLETE && op_result(lookup)==id && W.tab.sold);
    while(op_status(grower)==OP_RUNNING) op_step(grower,1);
    assert(op_status(grower)==OP_COMPLETE && !W.tab.sold);
    w=rec_words(id,&n); assert(n==64); for(size_t i=0;i<n;i++) assert(w[i]==a[i]);
    assert(intern_sync(a,64,NULL)==id);
    printf("writer before/after copy cursor: mirrored=1; framed lookup during relocation=1; final payload correct and canonical=1\n");
    op_release(writer);op_release(grower);op_release(lookup);
    work_free();compiler_free();check_free();eval_free();machine_free();return 0;
}
