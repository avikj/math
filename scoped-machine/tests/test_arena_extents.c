/* BOUNDS-COMPLETION §5 acceptance: tiny extents cross several growth
 * boundaries; old references stay valid; dirty blocks are reused after
 * bounded clearing; a repeated allocate/retire workload reaches a stable
 * owned footprint; production results do not depend on the extent size.
 * Run: test_arena_extents */
#include "check.h"
#include "lib.h"
#include "arena.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

int main(void) {
    setvbuf(stdout, NULL, _IONBF, 0);
    arena_set_extent_policy(ARENA_PAGE * 4);   /* four pages per extent: a growth policy, not a capacity */
    arena_init();
    size_t e0 = arena_extents();
    enum { N = 100 };
    uint64_t *blk[N]; size_t got[N];
    for (size_t i = 0; i < N; i++) { blk[i] = arena_alloc(ARENA_PAGE, &got[i]); for (size_t j = 0; j < got[i]; j++) blk[i][j] = (i << 20) | j; }
    size_t grown = arena_extents() - e0;
    int bad = 0;
    for (size_t i = 0; i < N; i++) for (size_t j = 0; j < got[i]; j++) if (blk[i][j] != ((i << 20) | j)) bad++;
    printf("extents: %zu growth boundaries crossed; old blocks intact=%d\n", grown, bad == 0);
    /* a block larger than the policy gets its own extent */
    size_t gbig; uint64_t *big = arena_alloc(ARENA_PAGE * 64, &gbig); for (size_t j = 0; j < gbig; j++) big[j] = j;
    for (size_t j = 0; j < gbig; j++) if (big[j] != j) bad++;
    /* released blocks are DIRTY_FREE; zero requests take them after bounded clearing */
    for (size_t i = 0; i < N; i += 2) arena_release(blk[i], got[i]);
    size_t steps = 0; while (arena_tend_zero()) steps++;
    ArenaZeroStats z0 = arena_zero_stats();
    size_t zbad = 0; uint64_t *zs[N / 2]; size_t zg[N / 2];
    for (size_t i = 0; i < N / 2; i++) { zs[i] = arena_alloc_zero(ARENA_PAGE, &zg[i]); for (size_t j = 0; j < zg[i]; j++) if (zs[i][j]) zbad++; }
    ArenaZeroStats z1 = arena_zero_stats();
    printf("dirty reuse: clearing steps=%zu (32 words each) reused=%llu nonzero words=%zu sync-cleared=%llu\n", steps, (unsigned long long)(z1.reused - z0.reused), zbad, (unsigned long long)(z1.sync_words - z0.sync_words));
    for (size_t i = 0; i < N / 2; i++) arena_release(zs[i], zg[i]);
    for (size_t i = 1; i < N; i += 2) arena_release(blk[i], got[i]);
    arena_release(big, gbig);
    /* repeated allocate/retire: the owned footprint stops growing */
    size_t foot[4];
    for (int round = 0; round < 200; round++) {
        uint64_t *b[40]; size_t g[40];
        for (int i = 0; i < 40; i++) b[i] = (i & 1) ? arena_alloc_zero(ARENA_PAGE << (i % 3), &g[i]) : arena_alloc(ARENA_PAGE << (i % 3), &g[i]);
        for (int i = 0; i < 40; i++) arena_release(b[i], g[i]);
        for (int i = 0; i < 64; i++) arena_tend_zero();
        if (round == 10) foot[0] = arena_owned_words();
        if (round == 199) foot[1] = arena_owned_words();
    }
    printf("footprint: after 10 rounds=%zu words, after 200 rounds=%zu words (stable=%d)\n", foot[0], foot[1], foot[0] == foot[1]);
    /* production results with tiny extents */
    machine_init(); eval_init(); check_init();
    RefId U = mk_universe(0); TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
    CtxDecl ds[] = { { S_TERM, va, U }, { S_TERM, vx, A } }; ContextId G = context_make(2, ds, fc_true());
    const char *why = NULL;
    CheckStatus st = check(G, fc_true(), mk_refl(0, A, x), mk_path_const(0, A, x, x), &why);
    printf("production check under tiny extents: %s (extents now %zu)\n", st == CK_VALID ? "VALID" : "not valid", arena_extents());
    check_free(); eval_free(); machine_free();
    return bad == 0 && grown >= 20 && zbad == 0 && foot[0] == foot[1] && st == CK_VALID && z1.reused > z0.reused ? 0 : 1;
}
