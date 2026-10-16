#include "runtime.h"
#include <assert.h>
int main(void) {
    machine_init();eval_init();check_init();compiler_init();check_set_budget(0);
    ContextId G=context_make(0,NULL,fc_true());RefId T;
    RefId N=rt_node_fun(2,0,0,&T);const char *why="";uint64_t level=0;
    CheckStatus formation=check_is_type(G,fc_true(),T,&level,&why);
    printf("node_(2,0,0) signature formation=%s level=%llu\n",check_status_name(formation),(unsigned long long)level);
    assert(formation==CK_VALID);
    CheckStatus st=check(G,fc_true(),N,T,&why);
    printf("node_(2,0,0) body=%s reason=%s\n",check_status_name(st),why?why:"");
    compiler_free();check_free();eval_free();machine_free();return st!=CK_VALID;
}
