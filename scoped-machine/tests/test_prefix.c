/* §84.2 committed prefixes (PREFIX-CONTRACT.md §6): the contract's further
 * cases beyond review_live_prefix.c.
 *   nested    — a beta prefix under two pending eliminators is lifted (CONTEXT)
 *               and the specialized endpoint finishes without replaying it
 *   deps      — a structural prefix records no premise on the pending global;
 *               a prefix through an unfolded global records its revision
 *   face      — a prefix under j=0 is not used under true; it is under j=0
 *   joined    — two clients of one specialized key: one adapter computation,
 *               two deliveries, no repeated source rule
 *   schedules — FIFO/LIFO/random policies and a worker pool give the same
 *               answers with no repeated source rule
 *   proofuse  — the operational prefix of a recursive program is not logical
 *               evidence: the proof-use audit still answers PENDING
 * Run: test_prefix {nested|deps|face|joined|schedules|proofuse|all} */
#include "check.h"
#include "lib.h"
#include "proof.h"
#include "compiler.h"
#include "reuse_stats.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

typedef struct { RefId U, A, x; TermVarId va, vx; DimVarId i, j; SymbolId loop, k; RefId f2; ContextId G; } World;

static void world(World *w) {
    w->U = mk_universe(0);
    w->va = declare_term(w->U, fc_true()); w->A = ref_var(w->va);
    w->vx = declare_term(w->A, fc_true()); w->x = ref_var(w->vx);
    w->i = declare_dim(); w->j = declare_dim();
    uint64_t pars[] = { w->va, w->vx };
    /* p : Path A x x with body p (operationally typed, pending) */
    w->loop = define_global("pending_path", varset_make(pars, 2), dimset_make(NULL, 0), mk_path_const(0, w->A, w->x, w->x));
    assert(w->loop && set_global_body(w->loop, global_ref(w->loop)));
    /* f2 = λa b. a : A → A → A;  k : Path (A→A→A) f2 f2 with body k */
    TermVarId a = declare_term(w->A, fc_true()), b = declare_term(w->A, fc_true());
    w->f2 = mk_lam_lv(0, a, w->A, mk_lam_lv(0, b, w->A, ref_var(a)));
    RefId F2 = mk_fun(0, 0, w->A, mk_fun(0, 0, w->A, w->A));
    w->k = define_global("pending_fun_path", varset_make(pars, 2), dimset_make(NULL, 0), mk_path_const(0, F2, w->f2, w->f2));
    assert(w->k && set_global_body(w->k, global_ref(w->k)));
    CtxDecl ds[] = { { S_TERM, w->va, w->U }, { S_TERM, w->vx, w->A }, { S_DIM, w->i, 0 }, { S_DIM, w->j, 0 } };
    w->G = context_make(4, ds, fc_true());
}
static RefId p_at(World *w, IntervalId s) { return mk_papp_const(0, w->A, w->x, w->x, global_ref(w->loop), s); }
static RefId simple_term(World *w) {   /* (λz. p@i) x */
    TermVarId z = declare_term(w->A, fc_true());
    return mk_app(mk_lam_lv(0, z, w->A, p_at(w, iv_var(w->i))), w->x);
}
static RefId nested_term(World *w) {   /* (((λz. k@i) x) x) x */
    TermVarId z = declare_term(w->A, fc_true());
    RefId F2 = mk_fun(0, 0, w->A, mk_fun(0, 0, w->A, w->A));
    RefId kat = mk_papp_const(0, F2, w->f2, w->f2, global_ref(w->k), iv_var(w->i));
    return mk_app(mk_app(mk_app(mk_lam_lv(0, z, w->A, kat), w->x), w->x), w->x);
}
static RefId at0(RefId t, DimVarId i) { MapBuilder m; mapb_init(&m); mapb_dim(&m, i, iv_zero()); return reindex(t, mapb_finish(&m)); }
static void start(void) { machine_init(); eval_init(); check_init(); compiler_init(); }
static void stop(void) { compiler_free(); check_free(); eval_free(); machine_free(); }

/* observe t generically (pending), then the instance; returns the betas the instance added */
static uint64_t generic_then(RefId t, FaceId gface, RefId target, FaceId face, RefId expect, EntryId *src, EntryId *tgt, const char *what) {
    uint64_t b0 = reuse_count(REUSE_BETA);
    WhnfStatus s0; EvalResult *r0 = whnf(t, gface, &s0);
    EXPECT(s0 == W_STUCK && !r0, "%s: generic source pending", what);
    (void)b0;
    *src = eval_entry_lookup(t, gface);
    EXPECT(*src && eval_entry_state(*src) == E_RUNNING, "%s: source RUNNING", what);
    EXPECT(*src && !eval_entry_residual(*src) && !eval_entry_receipt(*src), "%s: no final answer fabricated", what);
    uint64_t before = reuse_count(REUSE_BETA);
    WhnfStatus s1; EvalResult *r1 = whnf(target, face, &s1);
    EXPECT(s1 == W_OK && r1 && r1->ref == expect, "%s: instance answer (status %d, class %d)", what, (int)s1, r1 ? (int)r1->cls : -1);
    *tgt = eval_entry_lookup(target, face);
    EXPECT(*src && eval_entry_state(*src) == E_RUNNING, "%s: source still RUNNING", what);
    return reuse_count(REUSE_BETA) - before;
}

static void t_nested(bool restrict_face) {
    start(); World w; world(&w);
    RefId t = nested_term(&w);
    const char *why = NULL;
    EXPECT(check(w.G, fc_true(), t, w.A, &why) == CK_VALID, "nested term checks (%s)", why ? why : "");
    RefId target = restrict_face ? t : at0(t, w.i); FaceId face = restrict_face ? fc_lit(w.i, 0) : fc_true();
    EntryId src, tgt;
    uint64_t betas = generic_then(t, fc_true(), target, face, w.x, &src, &tgt, "nested");
    const PrefixFact *f = eval_entry_prefix(src);
    EXPECT(f && f->source == t && f->src == src, "nested: the outer producer holds a lifted fact");
    EXPECT(f && f->origin != src, "nested: the outer fact was lifted (CONTEXT), its first step committed below");
    EXPECT(betas == 2, "nested: the instance runs only f2's two betas, not the lifted one (got %llu)", (unsigned long long)betas);
    EXPECT(tgt && eval_entry_adapter_fact(tgt) == f, "nested: the instance continued from the pinned outer fact");
    EvalPrefixEvents pe = eval_prefix_events();
    EXPECT(pe.lifted >= 2, "nested: two CONTEXT lifts (got %zu)", pe.lifted);
    printf("nested %s: betas=%llu lifted=%zu published=%zu notify=%zu adapters=%zu\n", restrict_face ? "restrict" : "specialize",
           (unsigned long long)betas, pe.lifted, pe.published, pe.notify_steps, pe.adapters);
    stop();
}

static void t_deps(void) {
    start(); World w; world(&w);
    RefId t = simple_term(&w);
    EntryId src, tgt;
    uint64_t betas = generic_then(t, fc_true(), at0(t, w.i), fc_true(), w.x, &src, &tgt, "deps/structural");
    EXPECT(betas == 0, "deps/structural: no repeated beta");
    const PrefixFact *f = eval_entry_prefix(src);
    bool reads_loop = false;
    for (size_t k = 0; f && k + 1 < f->ngdeps; k += 2) if (f->gdeps[k] == w.loop) reads_loop = true;
    EXPECT(f && !reads_loop, "deps/structural: the beta prefix has no premise on the pending global's body");
    EXPECT(f && eval_prefix_valid(f), "deps/structural: premises current");
    /* through an unfolded global: F := λz. p@i */
    uint64_t pars[] = { w.va, w.vx }, dims[] = { w.i };
    TermVarId z = declare_term(w.A, fc_true());
    SymbolId F = define_global("unfolded", varset_make(pars, 2), dimset_make(dims, 1), mk_fun(0, 0, w.A, w.A));
    assert(F && set_global_body(F, mk_lam_lv(0, z, w.A, p_at(&w, iv_var(w.i)))));
    RefId t2 = mk_app(global_ref(F), w.x);
    EntryId src2, tgt2;
    betas = generic_then(t2, fc_true(), at0(t2, w.i), fc_true(), w.x, &src2, &tgt2, "deps/unfold");
    EXPECT(betas == 0, "deps/unfold: no repeated beta");
    const PrefixFact *f2 = eval_entry_prefix(src2);
    bool reads_F = false;
    for (size_t k = 0; f2 && k + 1 < f2->ngdeps; k += 2) if (f2->gdeps[k] == F && f2->gdeps[k + 1] == global_revision(F)) reads_F = true;
    EXPECT(f2 && reads_F, "deps/unfold: the prefix records the unfolded global's revision");
    EXPECT(f2 && eval_prefix_valid(f2), "deps/unfold: premises current");
    printf("deps: structural premises=%zu unfold premises=%zu\n", f ? f->ngdeps / 2 : 0, f2 ? f2->ngdeps / 2 : 0);
    stop();
}

static void t_face(void) {
    start(); World w; world(&w);
    TermVarId z = declare_term(w.A, fc_true());
    RefId rj = mk_papp_const(0, w.A, w.x, w.x, mk_refl(0, w.A, w.x), iv_var(w.j));
    RefId t = mk_app(mk_lam_lv(0, z, w.A, p_at(&w, iv_var(w.i))), rj);   /* support {i, j} */
    FaceId j0 = fc_lit(w.j, 0);
    WhnfStatus s0; EXPECT(!whnf(t, j0, &s0) && s0 == W_STUCK, "face: generic under j=0 pending");
    EntryId src = eval_entry_lookup(t, j0);
    EXPECT(src && eval_entry_prefix(src) && eval_entry_prefix(src)->face == j0, "face: the fact carries j=0");
    RefId target = at0(t, w.i);
    /* under j=0 first (a READY instance at j=0 is then no candidate under true either) */
    uint64_t b = reuse_count(REUSE_BETA);
    WhnfStatus s2; EvalResult *r2 = whnf(target, j0, &s2);
    EntryId t0 = eval_entry_lookup(target, j0);
    EXPECT(s2 == W_OK && r2 && r2->ref == w.x, "face: instance under j=0 answers");
    EXPECT(t0 && eval_entry_adapter_fact(t0) == eval_entry_prefix(src), "face: under j=0 the fact is used");
    EXPECT(reuse_count(REUSE_BETA) - b == 0, "face: under j=0 no repeated beta");
    b = reuse_count(REUSE_BETA);
    WhnfStatus s1; EvalResult *r1 = whnf(target, fc_true(), &s1);
    EntryId tt = eval_entry_lookup(target, fc_true());
    EXPECT(s1 == W_OK && r1 && r1->ref == w.x, "face: instance under true answers");
    EXPECT(tt && !eval_entry_adapter_fact(tt) && !eval_entry_adapter_source(tt), "face: neither the j=0 fact nor the j=0 answer is used under true");
    EXPECT(reuse_count(REUSE_BETA) - b == 1, "face: under true the beta is performed (no stronger face leaks)");
    printf("face: true-adapter=%d j0-adapter=%d\n", tt && eval_entry_adapter_fact(tt) != NULL, t0 && eval_entry_adapter_fact(t0) != NULL);
    stop();
}

static int delivered;
static void on_deliver(void *ctx, EvalResult *r) { (void)ctx; if (r && r->cls != R_INVALID) __atomic_add_fetch(&delivered, 1, __ATOMIC_SEQ_CST); }
static void t_joined(void) {
    start(); World w; world(&w);
    RefId t = simple_term(&w);
    WhnfStatus s0; EXPECT(!whnf(t, fc_true(), &s0) && s0 == W_STUCK, "joined: generic pending");
    RefId target = at0(t, w.i);
    uint64_t b = reuse_count(REUSE_BETA), ad0 = eval_prefix_events().adapters;
    delivered = 0;
    eval_request(target, fc_true(), cont_external(on_deliver, NULL, NULL));
    eval_request(target, fc_true(), cont_external(on_deliver, NULL, NULL));
    eval_run();
    EntryId e = eval_entry_lookup(target, fc_true());
    size_t req, del, pub; eval_entry_events(e, &req, &del, &pub);
    EXPECT(delivered == 2 && req == 2 && del == 2 && pub == 1, "joined: two requests, two deliveries, one publication (req=%zu del=%zu pub=%zu delivered=%d)", req, del, pub, delivered);
    EXPECT(eval_entry_runs(e) <= 1 && eval_prefix_events().adapters - ad0 == 1, "joined: one shared adapter computation");
    EXPECT(reuse_count(REUSE_BETA) == b, "joined: no repeated source rule");
    printf("joined: req=%zu deliveries=%zu publications=%zu adapters=%zu\n", req, del, pub, (size_t)(eval_prefix_events().adapters - ad0));
    stop();
}

static void t_schedules(void) {
    for (int pol = 0; pol < 3; pol++) for (uint64_t seed = 1; seed <= (pol == 2 ? 16u : 1u); seed++) for (int nested = 0; nested < 2; nested++) {
        start(); World w; world(&w);
        eval_set_policy((SchedPolicy)pol, seed);
        RefId t = nested ? nested_term(&w) : simple_term(&w);
        EntryId src, tgt;
        uint64_t betas = generic_then(t, fc_true(), at0(t, w.i), fc_true(), w.x, &src, &tgt, "schedules");
        EXPECT(betas == (nested ? 2u : 0u), "schedules: policy %d seed %llu nested %d betas %llu", pol, (unsigned long long)seed, nested, (unsigned long long)betas);
        stop();
    }
    for (int nested = 0; nested < 2; nested++) {
        start(); World w; world(&w); eval_set_workers(4);
        RefId t = nested ? nested_term(&w) : simple_term(&w);
        EntryId src, tgt;
        uint64_t betas = generic_then(t, fc_true(), at0(t, w.i), fc_true(), w.x, &src, &tgt, "schedules/workers");
        EXPECT(betas == (nested ? 2u : 0u), "schedules: 4 workers nested %d betas %llu", nested, (unsigned long long)betas);
        stop();
    }
    printf("schedules: FIFO, LIFO, 16 random seeds, 4 workers\n");
}

static void t_proofuse(void) {
    start(); World w; world(&w);
    RefId t = simple_term(&w);
    WhnfStatus s0; EXPECT(!whnf(t, fc_true(), &s0) && s0 == W_STUCK, "proofuse: generic pending");
    EXPECT(eval_entry_prefix(eval_entry_lookup(t, fc_true())) != NULL, "proofuse: a prefix fact exists");
    ProofUse u = proof_use(w.G, fc_true(), t, w.A);
    EXPECT(u.status == PU_PENDING, "proofuse: the recursive program's prefix is not unconditional evidence (status %d)", (int)u.status);
    printf("proofuse: status=%s\n", proof_use_name(u.status));
    stop();
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    const char *m = argc > 1 ? argv[1] : "all";
    bool all = !strcmp(m, "all");
    if (all || !strcmp(m, "nested")) { t_nested(false); t_nested(true); }
    if (all || !strcmp(m, "deps")) t_deps();
    if (all || !strcmp(m, "face")) t_face();
    if (all || !strcmp(m, "joined")) t_joined();
    if (all || !strcmp(m, "schedules")) t_schedules();
    if (all || !strcmp(m, "proofuse")) t_proofuse();
    printf("test_prefix: %d failures\n", fails);
    return fails ? 1 : 0;
}
