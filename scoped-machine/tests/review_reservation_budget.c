#include "work.c"
#include <assert.h>

static int probe(size_t n) {
    uint64_t *key=malloc(n*sizeof *key);assert(key);key[0]=K_LIST;
    for(size_t i=1;i<n;i++)key[i]=1000000+n+i;
    OpId h=op_new(OF_INTERN,PH_REWRITE,fr_intern(key,n));
    size_t steps=0;
    while(top(JOB(HND(h)->job))->ph!=5) {
        assert(op_step(h,1)==OP_RUNNING);assert(++steps<4*n+1000);
    }
    /* Enough capacity already exists. Any payload writes in this unit are
       not allocator work, growth, page faults, or initial setup. */
    words_reserve(&W.tab.store,n+2);
    size_t off=W.tab.store.n;uint64_t *storage=W.tab.store.w;
    const uint64_t sentinel=UINT64_C(0x5a5a5a5a5a5a5a5a);
    for(size_t i=0;i<n+2;i++)storage[off+i]=sentinel;
    uint64_t before=op_frames(h);size_t records=W.tab.n;
    assert(op_step(h,1)==OP_RUNNING);
    assert(W.tab.store.w==storage);assert(W.tab.n==records);
    size_t writes=0;
    for(size_t i=0;i<n;i++)if(storage[off+2+i]!=sentinel)writes++;
    printf("reserve n=%zu budget=1 units=%llu payload_words_written=%zu capacity_already_present=1\n",
           n,(unsigned long long)(op_frames(h)-before),writes);
    while(op_status(h)==OP_RUNNING)op_step(h,1);
    assert(op_status(h)==OP_COMPLETE);uint64_t id=op_result(h);size_t m;
    const uint64_t *got=rec_words(id,&m);assert(m==n);
    for(size_t i=0;i<n;i++)assert(got[i]==key[i]);
    assert(intern_sync(key,n,NULL)==id);
    printf("completed record correct and canonical=1\n");
    op_release(h);free(key);return writes>CHUNK_WORDS;
}
int main(void) {
    machine_init();eval_init();check_init();compiler_init();work_init();
    int bad=probe(64)+probe(4096);
    work_free();compiler_free();check_free();eval_free();machine_free();return bad?1:0;
}
