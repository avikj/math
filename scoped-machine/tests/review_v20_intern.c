#include "intern.h"
#include "kcont.h"
#include "fine.h"
#include "arena.h"
#include <assert.h>
static Interner T;
static uint64_t hash(uint64_t x){uint64_t h=1469598103934665603ULL;for(int i=0;i<8;i++){h^=x&255;h*=1099511628211ULL;x>>=8;}h^=1;h*=1099511628211ULL;return h?h:1;}
static void lookup(KCont*k){k->out[0]=interner_find(&T,k->arg,1);k->ok=true;}
int main(int argc,char**argv){setvbuf(stdout,NULL,_IONBF,0);size_t n=argc>1?strtoull(argv[1],NULL,10):300;assert(n<512);interner_init(&T);size_t have=0;uint64_t x=0;for(;have<n;x++)if((hash(x)&1023)==7){interner_intern(&T,&x,1,NULL);have++;}while((hash(x)&1023)!=7)x++;
 KCont*k=kc_new(lookup,&x,1);size_t max=0,units=0;while(!kc_done(k)){size_t u=kc_grant(k,1);if(u>max)max=u;units++;}
 printf("collision chain n=%zu units=%zu max_transitions=%zu result=%llu\n",n,units,max,(unsigned long long)k->out[0]);int ok=max<=128&&!k->out[0];kc_free(k);kc_shutdown();interner_free(&T);return ok?0:1;}
