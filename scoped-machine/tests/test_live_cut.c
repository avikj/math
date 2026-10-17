/* LIVE-CUT-ADOPTION §7: adoption of a newly committed fact at an already
 * RUNNING producer's committed cut, through the evaluator's actual
 * producer / continuation path.
 *
 *   pending     — an instance whose slot is waiting on a held child adopts a
 *                 generic source's later fact and finishes without the
 *                 generic suffix and without replaying the prefix; the old
 *                 ticket's delivery is consumed with no semantic resume
 *   race-deliver— the proposal is prepared, its installation held, the slot
 *                 advanced by the ordinary delivery: the installation fails
 *   race-adopt  — adoption first, then the old ticket's delivery; again with
 *                 a join slot whose sibling stays pending (the join does not
 *                 publish: the slot was filled exactly once)
 *   multi       — two proposals at one generation (two facts of one source):
 *                 at most one installs; two clients of the adapted key share
 *                 its producer with distinct requests and deliveries
 *   premise     — an unrelated environment change before installation:
 *                 revalidated and installed; a used premise invalidated
 *                 before installation: revalidation fails, the slot finishes
 *                 by its ordinary delivery; a structural prefix unaffected by
 *                 the change is still adopted afterwards
 *   guards      — a branch fact (guard i=1) is adopted under i=1 and not under
 *                 a face without it; a family fact under j=0 (j bound by the
 *                 composition) is not adopted by the composition's slot
 *   budget      — the pending case under one-job budgets: every
 *                 administrative job is one step owned by the slot's producer,
 *                 with the same outcome and event counts as an unbudgeted run
 *   teardown    — clients released, then the machine freed with old and
 *                 current tickets pending and jobs held; an external consumer
 *                 is delivered exactly once across adoption and the
 *                 superseded delivery
 *   edge        — an instantiation edge recorded after the slot subscribed
 *                 registers a new watch (history replayed) and the slot adopts
 * Run: test_live_cut {pending|race-deliver|race-adopt|multi|premise|guards|budget|teardown|edge|all} [workers] [fifo|lifo|random] */
#include "check.h"
#include "lib.h"
#include "compiler.h"
#include "reuse_stats.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static size_t g_workers; static SchedPolicy g_policy = POL_FIFO;
typedef struct { RefId U, A, x; TermVarId va, vx; DimVarId i, j; SymbolId loop; ContextId G; } World;

static void start(void) {
    machine_init(); eval_init(); check_init(); compiler_init();
    eval_set_policy(g_policy, 0x5EEDULL); eval_set_pair_policy(g_policy, 0x5EEDULL);
    if (g_workers) eval_set_workers(g_workers);
}
static void stop(void) { eval_set_hold(NULL, NULL); compiler_free(); check_free(); eval_free(); machine_free(); }
static void world(World *w) {
    w->U = mk_universe(0);
    w->va = declare_term(w->U, fc_true()); w->A = ref_var(w->va);
    w->vx = declare_term(w->A, fc_true()); w->x = ref_var(w->vx);
    w->i = declare_dim(); w->j = declare_dim();
    uint64_t pars[] = { w->va, w->vx };
    w->loop = define_global("pending_path", varset_make(pars, 2), dimset_make(NULL, 0), mk_path_const(0, w->A, w->x, w->x));
    assert(w->loop && set_global_body(w->loop, global_ref(w->loop)));
}
static RefId p_at(World *w, IntervalId s) { return mk_papp_const(0, w->A, w->x, w->x, global_ref(w->loop), s); }
static RefId simple_term(World *w, DimVarId d) { TermVarId z = declare_term(w->A, fc_true()); return mk_app(mk_lam_lv(0, z, w->A, p_at(w, iv_var(d))), w->x); }   /* (λz. p@d) x */
static SymbolId wrap(World *w, const char *name, RefId body, size_t nd, uint64_t *dims) {
    uint64_t pars[] = { w->va, w->vx };
    SymbolId s = define_global(name, varset_make(pars, 2), dimset_make(dims, nd), w->A);
    assert(s && set_global_body(s, body)); return s;
}
static RefId at0(RefId t, DimVarId i) { MapBuilder m; mapb_init(&m); mapb_dim(&m, i, iv_zero()); return reindex(t, mapb_finish(&m)); }

/* scheduler holds: by job kind, optionally restricted to the evaluation of one key */
typedef struct { bool on_key; RefId ref; FaceId face; bool installs; bool all_eval_of_ref2; RefId ref2; const PrefixFact *except_fact; } Hold;
static bool hold_pred(const EvalTaskInfo *in, void *ctx) {
    Hold *h = ctx;
    if (h->installs && in->kind == ET_INSTALL && (!h->except_fact || in->fact != h->except_fact)) return true;
    if (in->kind == ET_EVALUATE && in->producer) {
        if (h->on_key && eval_entry_ref(in->producer) == h->ref && eval_entry_face(in->producer) == h->face) return true;
        if (h->all_eval_of_ref2 && eval_entry_ref(in->producer) == h->ref2) return true;
    }
    return false;
}
static size_t count_betas(void) { return reuse_count(REUSE_BETA); }
static EvalCutEvents cev(void) { return eval_cut_events(); }
static bool receipt_names_fact(uint64_t r, uint64_t id, int depth) {
    if (!r || depth > 64) return false;
    size_t n; const uint64_t *w = eval_receipt_words(r, &n);
    if ((w[0] == RC_PREFIX_RESTRICT || w[0] == RC_PREFIX_SPEC) && w[1] == id) return true;
    if (w[0] == RC_SEQ) return receipt_names_fact(w[1], id, depth + 1) || receipt_names_fact(w[2], id, depth + 1);
    if (w[0] == RC_RULE) return receipt_names_fact(w[2], id, depth + 1);
    return false;
}
static bool receipt_has_prefix_adapter(uint64_t r, int depth) {
    if (!r || depth > 64) return false;
    size_t n; const uint64_t *w = eval_receipt_words(r, &n);
    if (w[0] == RC_PREFIX_RESTRICT || w[0] == RC_PREFIX_SPEC) return true;
    if (w[0] == RC_SEQ) return receipt_has_prefix_adapter(w[1], depth + 1) || receipt_has_prefix_adapter(w[2], depth + 1);
    if (w[0] == RC_RULE) return receipt_has_prefix_adapter(w[2], depth + 1);
    return false;
}

/* ---- 1 pending (and 3: adoption first, then the old delivery) ---- */
static void t_pending(bool spec) {
    start(); World w; world(&w);
    RefId term = simple_term(&w, w.i);
    uint64_t di[] = { w.i };
    SymbolId W = wrap(&w, "wrap", term, 1, di);
    RefId I = spec ? at0(global_ref(W), w.i) : global_ref(W);
    FaceId If = spec ? fc_true() : fc_lit(w.i, 0);
    RefId Jref = spec ? at0(term, w.i) : term;
    Hold h = { true, Jref, If, false, false, 0 };
    eval_set_hold(hold_pred, &h);
    WhnfStatus s; EvalResult *r = whnf(I, If, &s);
    EXPECT(s == W_STUCK && !r, "pending/%s: the instance waits on its held child", spec ? "spec" : "restrict");
    EntryId Ie = eval_entry_lookup(I, If);
    EXPECT(Ie && eval_entry_state(Ie) == E_RUNNING, "instance RUNNING");
    uint64_t b0 = count_betas();
    r = whnf(term, fc_true(), &s);                   /* the generic source commits its beta fact and stays pending */
    EXPECT(s == W_STUCK, "generic source pending");
    EntryId Ge = eval_entry_lookup(term, fc_true());
    EXPECT(Ge && eval_entry_state(Ge) == E_RUNNING && eval_entry_prefix(Ge), "generic RUNNING with a committed fact");
    EXPECT(eval_entry_state(Ie) == E_READY, "the instance finished by adoption while its old child is held");
    EvalResult *ri = whnf(I, If, &s);
    EXPECT(s == W_OK && ri && ri->ref == w.x, "instance answer x");
    EXPECT(count_betas() - b0 == 1, "only the generic's own beta was performed (instance replayed none): %zu", (size_t)(count_betas() - b0));
    EXPECT(receipt_has_prefix_adapter(eval_entry_receipt(Ie), 0), "the instance's receipt names the adopted prefix");
    EvalCutEvents c1 = cev();
    EXPECT(c1.installs == 1 && c1.deliveries_stale == 0, "one installation (installs=%zu stale=%zu)", c1.installs, c1.deliveries_stale);
    EntryId Je = eval_entry_lookup(Jref, If);
    EXPECT(Je && eval_entry_runs(Je) == 0, "the old child never ran (held)");
    { EntryId *act, *all; size_t na = eval_entry_active_deps(Ie, &act), nall = eval_entry_deps(Ie, &all);
      bool old_hist = true; for (size_t k = 0; k < na; k++) if (act[k] == Je) old_hist = false;
      EXPECT(nall == na + 1 && old_hist, "the superseded request is a historical edge (all=%zu active=%zu)", nall, na); free(act); free(all); }
    size_t req, del, pub; eval_entry_events(Ie, &req, &del, &pub);
    /* 3: the old ticket's delivery after adoption */
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    EXPECT(eval_entry_state(Je) == E_READY, "the old child completed after release");
    EvalCutEvents c2 = cev();
    EXPECT(c2.deliveries_stale == 1, "the superseded ticket's delivery is consumed (stale=%zu)", c2.deliveries_stale);
    size_t req2, del2, pub2; eval_entry_events(Ie, &req2, &del2, &pub2);
    EXPECT(pub2 == 1 && pub == 1, "the instance published exactly once");
    EXPECT(count_betas() - b0 == 2, "the old request's own beta is real work, counted once (%zu)", (size_t)(count_betas() - b0));
    printf("pending/%s workers=%zu: installs=%zu current=%zu stale=%zu resumes=%zu betas=%zu proposals=%zu rejected=%zu\n", spec ? "spec" : "restrict", g_workers,
           c2.installs, c2.deliveries_current, c2.deliveries_stale, c2.resumes, (size_t)(count_betas() - b0), c2.proposals, c2.prep_rejected);
    stop();
}

/* ---- 2 proposal prepared, installation held, ordinary delivery first ---- */
static void t_race_deliver(void) {
    start(); World w; world(&w);
    RefId term = simple_term(&w, w.i);
    uint64_t di[] = { w.i };
    SymbolId W = wrap(&w, "wrap", term, 1, di);
    RefId I = global_ref(W); FaceId If = fc_lit(w.i, 0);
    Hold h = { true, term, If, true, false, 0 };
    eval_set_hold(hold_pred, &h);
    WhnfStatus s; whnf(I, If, &s);
    whnf(term, fc_true(), &s);
    EntryId Ie = eval_entry_lookup(I, If);
    EvalCutEvents c0 = cev();
    EXPECT(eval_entry_state(Ie) == E_RUNNING && c0.installs == 0 && eval_held_count() >= 2, "prepared proposal held at installation (held=%zu)", eval_held_count());
    uint64_t b0 = count_betas();
    h.on_key = false;                                /* release the child; installations stay held */
    eval_release_held(); eval_run();
    EXPECT(eval_entry_state(Ie) == E_READY, "the slot advanced by its ordinary delivery");
    EXPECT(count_betas() - b0 == 1, "the child's beta was performed once");
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    EvalCutEvents c1 = cev();
    EXPECT(c1.installs == 0 && c1.install_not_waiting >= 1, "the installation failed the WAITING/generation check (not_waiting=%zu)", c1.install_not_waiting);
    EvalResult *r = whnf(I, If, &s);
    EXPECT(s == W_OK && r && r->ref == w.x && c1.resumes >= 1 && c1.deliveries_stale == 0, "result preserved; no superseded delivery");
    printf("race-deliver workers=%zu: installs=%zu not_waiting=%zu current=%zu stale=%zu betas_after_release=%zu\n", g_workers, c1.installs, c1.install_not_waiting, c1.deliveries_current, c1.deliveries_stale, (size_t)(count_betas() - b0));
    stop();
}

/* ---- 3b adoption into a join slot whose sibling stays pending ---- */
static void t_race_adopt_join(void) {
    start(); World w; world(&w);
    TermVarId z0 = declare_term(w.A, fc_true()), z1 = declare_term(w.A, fc_true());
    FaceId fs[2] = { fc_lit(w.i, 0), fc_lit(w.i, 1) };
    RefId ts[2] = { mk_lam_lv(0, z0, w.A, p_at(&w, iv_var(w.i))), mk_lam_lv(0, z1, w.A, p_at(&w, iv_var(w.j))) };
    RefId G = mk_app(ts[0], w.x);                                       /* (λz. p@i) x: branch 0's term */
    RefId Sys = mk_system(2, fs, ts);
    RefId B = mk_app(Sys, w.x);                                         /* branch 0: G under i=0 (held); branch 1: (λz. p@j) x, pending */
    FaceId cover = fc_join(fc_lit(w.i, 0), fc_lit(w.i, 1));            /* the system covers i=0 ∨ i=1 */
    Hold h = { true, G, fc_lit(w.i, 0), false, false, 0 };
    eval_set_hold(hold_pred, &h);
    WhnfStatus s; whnf(B, cover, &s);
    EntryId Be = eval_entry_lookup(B, cover);
    EXPECT(s == W_STUCK && Be && eval_entry_state(Be) == E_RUNNING, "join owner pending (s=%d Be=%llu)", (int)s, (unsigned long long)Be);
    whnf(G, fc_true(), &s);                                             /* the generic commits G ⇒ p@i */
    EvalCutEvents c1 = cev();
    EXPECT(c1.installs == 1 && c1.resumes >= 1, "the branch slot adopted (installs=%zu)", c1.installs);
    EXPECT(eval_entry_state(Be) == E_RUNNING, "the join waits for its pending sibling");
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    EvalCutEvents c2 = cev();
    EXPECT(c2.deliveries_stale == 1, "the old branch ticket's delivery is consumed (stale=%zu)", c2.deliveries_stale);
    EXPECT(eval_entry_state(Be) == E_RUNNING, "still pending: the branch slot was filled exactly once");
    printf("race-adopt/join workers=%zu: installs=%zu current=%zu stale=%zu owner_state=%d\n", g_workers, c2.installs, c2.deliveries_current, c2.deliveries_stale, (int)eval_entry_state(Be));
    stop();
}

/* ---- 4 several proposals at one generation; shared adapted producer ---- */
static void t_multi(void) {
    start(); World w; world(&w);
    RefId term = simple_term(&w, w.i);
    uint64_t di[] = { w.i };
    SymbolId F = wrap(&w, "source", term, 1, di);
    RefId Fr = global_ref(F);                                           /* facts: F ⇒ term (unfold), then F ⇒ p@i (lifted beta) */
    SymbolId W1 = wrap(&w, "client1", Fr, 1, di), W2 = wrap(&w, "client2", Fr, 1, di);
    RefId I1 = global_ref(W1), I2 = global_ref(W2); FaceId If = fc_lit(w.i, 0);
    Hold h = { true, Fr, If, true, false, 0 };
    eval_set_hold(hold_pred, &h);
    WhnfStatus s; whnf(I1, If, &s); whnf(I2, If, &s);
    whnf(Fr, fc_true(), &s);
    EntryId Fe = eval_entry_lookup(Fr, fc_true());
    EXPECT(eval_entry_prefix_count(Fe) >= 2, "the source committed two facts (%zu)", eval_entry_prefix_count(Fe));
    EvalCutEvents c0 = cev();
    EXPECT(c0.installs == 0 && c0.proposals >= 4, "both clients prepared proposals for both facts at their first generation (proposals=%zu)", c0.proposals);
    h.installs = false; eval_release_held(); eval_run();
    EvalCutEvents c1 = cev();
    EntryId I1e = eval_entry_lookup(I1, If), I2e = eval_entry_lookup(I2, If);
    EXPECT(eval_entry_state(I1e) == E_READY && eval_entry_state(I2e) == E_READY, "both clients finished by adoption");
    EXPECT(c1.install_stale_generation + c1.install_not_waiting >= 2, "the other proposal of each first generation failed the installation check (stale generation=%zu, slot no longer waiting=%zu)", c1.install_stale_generation, c1.install_not_waiting);
    /* the adapted key: the first installation's residual (the unfolded body or the beta residual) */
    RefId cand[2] = { term, p_at(&w, iv_var(w.i)) }; EntryId Ve = 0; size_t req = 0, del = 0, pub = 0;
    for (int c = 0; c < 2 && !Ve; c++) { EntryId e = eval_entry_lookup(cand[c], If); size_t a = 0, b = 0, d = 0; if (e) eval_entry_events(e, &a, &b, &d); if (e && a >= 2) { Ve = e; req = a; del = b; pub = d; } }
    EXPECT(Ve && eval_entry_runs(Ve) == 1 && req >= 2 && del >= 2 && pub == 1, "the adapted key's producer is shared: runs=%zu requests=%zu deliveries=%zu", Ve ? eval_entry_runs(Ve) : 0, req, del);
    printf("multi workers=%zu: proposals=%zu installs=%zu stale_generation=%zu not_waiting=%zu adapted key runs=%zu requests=%zu deliveries=%zu\n", g_workers, c1.proposals, c1.installs, c1.install_stale_generation, c1.install_not_waiting, Ve ? eval_entry_runs(Ve) : 0, req, del);
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    /* detachment: both clients resumed, so their first generations' subscriptions on the source's shape are
     * dead; a later publication on that shape detaches them from the list and frees them (their Cuts with them) */
    { EvalCutEvents d0 = cev();
      SymbolId W3 = wrap(&w, "client3", Fr, 1, di); FaceId If2 = fc_lit(w.i, 1);
      WhnfStatus s3; whnf(global_ref(W3), If2, &s3); whnf(Fr, If2, &s3); eval_run();
      EvalCutEvents d1 = cev();
      EXPECT(d1.subs_unlinked >= d0.subs_unlinked + 2 && d1.subs_freed >= d0.subs_freed + 2 && d1.cuts_freed > d0.cuts_freed,
             "dead subscriptions are detached and freed by a later publication on their shape, releasing their Cuts (unlinked=%zu freed=%zu cuts freed=%zu)",
             d1.subs_unlinked - d0.subs_unlinked, d1.subs_freed - d0.subs_freed, d1.cuts_freed - d0.cuts_freed);
      printf("multi detach workers=%zu: subscriptions unlinked=%zu freed=%zu cuts freed=%zu (live subscriptions now %zu of %zu)\n", g_workers,
             d1.subs_unlinked - d0.subs_unlinked, d1.subs_freed - d0.subs_freed, d1.cuts_freed - d0.cuts_freed, d1.subscriptions - d1.subs_freed, d1.subscriptions); }
    stop();
}

/* ---- 5 / 6 premise invalidation, branch guards, composition guards ---- */
typedef struct { RefId R, O_ref; SymbolId O, W5; } RWorld;
static void rworld(World *w, RWorld *q) {
    uint64_t pars[] = { w->va, w->vx };
    RefId F3 = mk_fun(0, 0, w->A, mk_fun(0, 0, w->A, w->A));
    q->O = define_global("opaque", varset_make(pars, 2), dimset_make(NULL, 0), F3); assert(q->O);
    q->O_ref = global_ref(q->O);
    TermVarId z = declare_term(w->A, fc_true()), y = declare_term(w->A, fc_true());
    FaceId fs[2] = { fc_lit(w->i, 0), fc_lit(w->i, 1) };
    RefId ts[2] = { q->O_ref, mk_lam_lv(0, z, w->A, mk_lam_lv(0, y, w->A, p_at(w, iv_var(w->j)))) };
    q->R = mk_app(mk_app(mk_system(2, fs, ts), w->x), w->x);          /* ([i=0 ↦ O, i=1 ↦ λz y. p@j] x) x */
    uint64_t dij[] = { w->i, w->j };
    q->W5 = wrap(w, "rclient", q->R, 2, dij);
}
static void t_premise(void) {
    start(); World w; world(&w); RWorld q; rworld(&w, &q);
    FaceId cover = fc_join(fc_lit(w.i, 0), fc_lit(w.i, 1));
    WhnfStatus s; whnf(q.R, cover, &s);
    EntryId Re = eval_entry_lookup(q.R, cover);
    const PrefixFact *bf = Re ? eval_entry_prefix(Re) : NULL;
    bool has_O = false; if (bf) for (size_t k = 0; k + 1 < bf->ngdeps; k += 2) if (bf->gdeps[k] == q.O) has_O = true;
    EXPECT(bf && has_O, "R's branch fact records the opaque symbol's revision as a premise");
    RefId I = global_ref(q.W5);
    /* (a) an unrelated environment change between preparation and installation */
    FaceId f11 = fc_meet(fc_lit(w.i, 1), fc_lit(w.j, 1));
    Hold h = { true, q.R, f11, true, false, 0, NULL };
    eval_set_hold(hold_pred, &h);
    whnf(I, f11, &s);
    EntryId Ia = eval_entry_lookup(I, f11);
    EXPECT(eval_entry_state(Ia) == E_RUNNING && cev().installs == 0, "(a) proposals held at installation");
    uint64_t pars[] = { w.va, w.vx };
    SymbolId Z = define_global("unrelated", varset_make(pars, 2), dimset_make(NULL, 0), w.A); assert(Z);
    h.installs = false; eval_release_held(); eval_run();
    EvalCutEvents ca = cev();
    EXPECT(ca.revalidations >= 1 && ca.revalidation_failed == 0 && ca.installs >= 1 && eval_entry_state(Ia) == E_READY, "(a) revalidated and installed (revalidations=%zu installs=%zu)", ca.revalidations, ca.installs);
    /* (b) a used premise invalidated before installation: only the proposal of
     * the fact carrying (opaque, revision) is let through to installation */
    FaceId f10 = fc_meet(fc_lit(w.i, 1), fc_lit(w.j, 0));
    h.face = f10; h.installs = true; h.except_fact = NULL;
    whnf(I, f10, &s);
    EntryId Ib = eval_entry_lookup(I, f10);
    EXPECT(eval_entry_state(Ib) == E_RUNNING, "(b) instance pending with its proposals held");
    TermVarId a = declare_term(w.A, fc_true()), b = declare_term(w.A, fc_true());
    EXPECT(set_global_body(q.O, mk_lam_lv(0, a, w.A, mk_lam_lv(0, b, w.A, ref_var(a)))), "the opaque symbol receives a body (its revision changes)");
    size_t rf0 = cev().revalidation_failed;
    h.except_fact = bf;                              /* every other installation stays held */
    eval_release_held(); eval_run();
    EvalCutEvents cb = cev();
    { EntryId *act, *all; size_t na = eval_entry_active_deps(Ib, &act), nall = eval_entry_deps(Ib, &all);
      EXPECT(cb.revalidation_failed == rf0 + 1 && na == nall && eval_entry_state(Ib) == E_RUNNING,
             "(b) the stale proposal fails revalidation and is not installed (revalidation_failed=%zu, requests=%zu active=%zu)", cb.revalidation_failed - rf0, nall, na);
      free(act); free(all); }
    /* then the remaining proposals (structural facts with no premise on the
     * opaque symbol) and the held child */
    h.on_key = false; h.installs = false;
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    EvalResult *r = whnf(I, f10, &s);
    EXPECT(s == W_OK && r && r->ref == w.x, "(b) the slot finished");
    /* the held child was launched (and may have continued from the fact by
     * the launch-time adapter) while the premise held; if its answer carries
     * the premise, that answer is not reusable in the new environment */
    { const uint64_t *pairs; size_t np = eval_entry_gdeps(Ib, &pairs); bool stale = false;
      for (size_t k = 0; k < np; k++) if (pairs[2 * k] == q.O && pairs[2 * k + 1] == 1) stale = true;
      EXPECT(!stale || !eval_entry_deps_valid(Ib), "(b) an answer carrying the stale premise is not valid for reuse");
      printf("premise (b): answer carries the stale premise=%d (via the child's launch-time adapter=%d), valid for reuse=%d\n", stale, receipt_names_fact(eval_entry_receipt(Ib), bf->id, 0), eval_entry_deps_valid(Ib)); }
    /* (c) a structural prefix unaffected by the change is still adopted */
    RefId term = simple_term(&w, w.i);
    uint64_t di[] = { w.i };
    SymbolId W = wrap(&w, "wrap_after", term, 1, di);
    Hold h2 = { true, term, fc_lit(w.i, 0), false, false, 0, NULL };
    eval_set_hold(hold_pred, &h2);
    whnf(global_ref(W), fc_lit(w.i, 0), &s);
    size_t inst1 = cev().installs;
    whnf(term, fc_true(), &s);
    EntryId Ic = eval_entry_lookup(global_ref(W), fc_lit(w.i, 0));
    EXPECT(eval_entry_state(Ic) == E_READY && cev().installs > inst1, "(c) the structural beta prefix is adopted after the body change");
    printf("premise workers=%zu: revalidations=%zu revalidation_failed=%zu installs=%zu\n", g_workers, cev().revalidations, cev().revalidation_failed, cev().installs);
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    stop();
}
static void t_guards(void) {
    start(); World w; world(&w); RWorld q; rworld(&w, &q);
    FaceId cover = fc_join(fc_lit(w.i, 0), fc_lit(w.i, 1));
    WhnfStatus s; whnf(q.R, cover, &s);
    RefId I = global_ref(q.W5);
    /* a face without i=1: the branch fact is partial there and is not adopted */
    FaceId fj = fc_meet(cover, fc_lit(w.j, 0));
    Hold h = { true, q.R, fj, false, false, 0 };
    eval_set_hold(hold_pred, &h);
    size_t i0 = cev().installs;
    whnf(I, fj, &s);
    EntryId Ij = eval_entry_lookup(I, fj);
    { EntryId *act, *all; size_t na = eval_entry_active_deps(Ij, &act), nall = eval_entry_deps(Ij, &all);
      EXPECT(eval_entry_state(Ij) == E_RUNNING && na == nall, "the guarded branch fact is not adopted without its guard (requests=%zu active=%zu)", nall, na); free(act); free(all); }
    /* under i=1 it is */
    FaceId f10 = fc_meet(fc_lit(w.i, 1), fc_lit(w.j, 0));
    h.face = f10;
    whnf(I, f10, &s);
    EntryId Ib = eval_entry_lookup(I, f10);
    EXPECT(eval_entry_state(Ib) == E_READY && cev().installs > i0, "the guarded branch fact is adopted under i=1");
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    EvalResult *rj = whnf(I, fj, &s);
    EXPECT(s == W_OK && rj && rj->cls == R_SYSTEM, "the total observation without i=1 is the system computed by its own child");
    /* composition: the family's fact under j=0 (j bound) is not adopted by the composition's slot */
    uint64_t pa[] = { w.va };
    SymbolId qt = define_global("pending_type_path", varset_make(pa, 1), dimset_make(NULL, 0), mk_path_const(1, w.U, w.A, w.A));
    assert(qt && set_global_body(qt, global_ref(qt)));
    RefId fam = mk_papp_const(1, w.U, w.A, w.A, global_ref(qt), iv_var(w.j));
    RefId C = mk_comp_lv(0, w.j, fam, fc_false(), w.x, w.x);
    whnf(fam, fc_lit(w.j, 0), &s);                                      /* the family's endpoint fact, guard j=0 */
    size_t i1 = cev().installs, rej1 = cev().prep_rejected;
    whnf(C, fc_true(), &s);
    EntryId Ce = eval_entry_lookup(C, fc_true());
    EXPECT(Ce && eval_entry_state(Ce) == E_RUNNING && cev().installs == i1, "the bound-dimension fact does not escape into the composition's observation");
    printf("guards workers=%zu: branch installs=%zu comp rejected proposals=%zu comp state=%d\n", g_workers, cev().installs, cev().prep_rejected - rej1, Ce ? (int)eval_entry_state(Ce) : -1);
    stop();
}

/* ---- 7 one-job budgets ---- */
typedef struct { size_t jobs[16], owned[16], unowned; EntryId owner; Hold h; } Probe;
static bool probe_pred(const EvalTaskInfo *in, void *ctx) {
    Probe *p = ctx;
    if (in->kind < 16) p->jobs[in->kind]++;
    if (p->owner && in->producer == p->owner && in->kind < 16) p->owned[in->kind]++;
    bool admin = in->kind == ET_SUBSCRIBE || in->kind == ET_REPLAY || in->kind == ET_NOTICE || in->kind == ET_PREPARE || in->kind == ET_INSTALL || in->kind == ET_REQUEST;
    if (admin && !in->producer) p->unowned++;
    return hold_pred(in, &p->h);
}
static void ext_store(void *ctx, EvalResult *r) { EvalResult **o = ctx; *o = r; }
static void run_pending_budget(bool budget, EvalCutEvents *out, RefId *ans, size_t *betas, size_t *max_prep_step, Probe *pr) {
    start(); World w; world(&w);
    RefId term = simple_term(&w, w.i);
    uint64_t di[] = { w.i };
    SymbolId W = wrap(&w, "wrap", term, 1, di);
    RefId I = global_ref(W); FaceId If = fc_lit(w.i, 0);
    memset(pr, 0, sizeof *pr); pr->h = (Hold){ true, term, If, false, false, 0 };
    eval_set_hold(probe_pred, pr);
    EvalResult *ri = NULL, *rg = NULL;
    eval_request(I, If, cont_external(ext_store, &ri, NULL));
    *max_prep_step = 0;
    if (budget) while (eval_run_budget(1)) {} else eval_run();
    pr->owner = eval_entry_lookup(I, If);
    size_t b0 = count_betas();
    eval_request(term, fc_true(), cont_external(ext_store, &rg, NULL));
    if (budget) { for (;;) { size_t p0 = cev().prep_steps; size_t n = eval_run_budget(1); size_t d = cev().prep_steps - p0; if (d > *max_prep_step) *max_prep_step = d; if (!n) break; } }
    else eval_run();
    *ans = ri ? ri->ref : 0; *betas = count_betas() - b0; *out = cev();
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    stop();
}
static void t_budget(void) {
    if (g_workers) { printf("budget: the budgeted scheduler is the sequential one (skipped with workers)\n"); return; }
    EvalCutEvents a, b; RefId ra, rb; size_t ba, bb, ma, mb; Probe pa, pb;
    run_pending_budget(false, &a, &ra, &ba, &ma, &pa);
    run_pending_budget(true, &b, &rb, &bb, &mb, &pb);
    EXPECT(ra && ra == rb && ba == bb && ba == 1, "same answer and betas under one-job budgets");
    EXPECT(a.installs == b.installs && a.proposals == b.proposals && a.prep_steps == b.prep_steps && a.subscriptions == b.subscriptions && a.replays == b.replays && a.notices == b.notices,
           "same administrative events (proposals %zu/%zu, prep steps %zu/%zu, subscriptions %zu/%zu)", a.proposals, b.proposals, a.prep_steps, b.prep_steps, a.subscriptions, b.subscriptions);
    EXPECT(mb <= 1, "each budgeted job advances at most one preparation step (%zu)", mb);
    EXPECT(pb.unowned == 0 && pb.owned[ET_INSTALL] == 1 && pb.owned[ET_REQUEST] == 1 && pb.owned[ET_PREPARE] >= 1,
           "every administrative job has its slot's producer as owner; the instance's installation and replacement request are the instance's (unowned=%zu install=%zu request=%zu)", pb.unowned, pb.owned[ET_INSTALL], pb.owned[ET_REQUEST]);
    printf("budget: answer equal=%d betas=%zu installs=%zu prep_steps=%zu max per job=%zu jobs: subscribe=%zu replay=%zu notice=%zu prepare=%zu install=%zu request=%zu\n",
           ra == rb, bb, b.installs, b.prep_steps, mb, pb.jobs[ET_SUBSCRIBE], pb.jobs[ET_REPLAY], pb.jobs[ET_NOTICE], pb.jobs[ET_PREPARE], pb.jobs[ET_INSTALL], pb.jobs[ET_REQUEST]);
}

/* ---- 8 teardown with old and current tickets pending ---- */
typedef struct { int delivered, freed; } Ext;
static void ext_count(void *ctx, EvalResult *r) { (void)r; ((Ext *)ctx)->delivered++; }
static void ext_free_ctx(void *ctx) { ((Ext *)ctx)->freed++; }
static void t_teardown(void) {
    /* (a) the adopted generation's child is also held: both tickets pending at teardown */
    { start(); World w; world(&w);
      RefId term = simple_term(&w, w.i);
      uint64_t di[] = { w.i };
      SymbolId W = wrap(&w, "wrap", term, 1, di);
      RefId I = global_ref(W); FaceId If = fc_lit(w.i, 0);
      Hold h = { true, term, If, false, true, p_at(&w, iv_var(w.i)) };
      eval_set_hold(hold_pred, &h);
      Ext e = { 0, 0 };
      eval_request(I, If, cont_external(ext_count, &e, ext_free_ctx));
      eval_run();
      WhnfStatus s; whnf(term, fc_true(), &s);
      EvalCutEvents c = cev();
      EXPECT(c.installs == 1 && e.delivered == 0, "(a) adopted; the new child is held too");
      printf("teardown/a workers=%zu: installs=%zu held=%zu external delivered=%d\n", g_workers, c.installs, eval_held_count(), e.delivered);
      stop();                                        /* eval_free with both tickets pending and jobs held */
      EXPECT(e.freed == 1 && e.delivered == 0, "(a) the external consumer is released, never delivered"); }
    /* (b) adoption delivers the external consumer once; the superseded delivery does not repeat it */
    { start(); World w; world(&w);
      RefId term = simple_term(&w, w.i);
      uint64_t di[] = { w.i };
      SymbolId W = wrap(&w, "wrap", term, 1, di);
      RefId I = global_ref(W); FaceId If = fc_lit(w.i, 0);
      Hold h = { true, term, If, false, false, 0 };
      eval_set_hold(hold_pred, &h);
      Ext e = { 0, 0 };
      eval_request(I, If, cont_external(ext_count, &e, ext_free_ctx));
      eval_run();
      WhnfStatus s; whnf(term, fc_true(), &s);
      EXPECT(e.delivered == 1, "(b) delivered once by adoption");
      eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
      EvalCutEvents c = cev();
      EXPECT(e.delivered == 1 && c.deliveries_stale == 1, "(b) the superseded ticket does not repeat the delivery");
      printf("teardown/b workers=%zu: external delivered=%d stale=%zu\n", g_workers, e.delivered, c.deliveries_stale);
      stop();
      EXPECT(e.freed == 0, "(b) a delivered consumer is not released again"); }
}

/* ---- an instantiation edge recorded after the slot subscribed ---- */
static void t_edge(void) {
    start(); World w; world(&w);
    RefId term = simple_term(&w, w.i);
    MapBuilder m; mapb_init(&m); mapb_dim(&m, w.i, iv_var(w.j)); RefId term2 = reindex(term, mapb_finish(&m));   /* (λz. p@j) x */
    RefId r = at0(term, w.i);                                           /* (λz. p@0) x; its recorded edge comes from term */
    uint64_t di[] = { w.i };
    SymbolId W = wrap(&w, "wrap", term, 1, di);
    RefId I = at0(global_ref(W), w.i);                                  /* unfolds to r */
    Hold h = { true, r, fc_true(), false, false, 0, NULL };
    eval_set_hold(hold_pred, &h);
    WhnfStatus s; whnf(I, fc_true(), &s);
    EntryId Ie = eval_entry_lookup(I, fc_true());
    whnf(term2, fc_true(), &s);                                         /* term2's fact: no edge relates it to r yet */
    EXPECT(eval_entry_state(Ie) == E_RUNNING && cev().installs == 0, "edge: no recorded correspondence, no adoption");
    size_t ew0 = cev().edge_watches;
    MapBuilder m2; mapb_init(&m2); mapb_dim(&m2, w.j, iv_zero());
    RefId r2 = reindex(term2, mapb_finish(&m2));                        /* records the edge r ← term2 */
    EXPECT(r2 == r, "edge: term2[j↦0] is the slot's residual");
    eval_run();
    EvalResult *ri = whnf(I, fc_true(), &s);
    EXPECT(cev().edge_watches > ew0 && cev().installs == 1 && s == W_OK && ri && ri->ref == w.x, "edge: the new edge registers a watch and the slot adopts term2's fact (watches %zu->%zu installs=%zu)", ew0, cev().edge_watches, cev().installs);
    printf("edge workers=%zu: watches=%zu installs=%zu answer x=%d\n", g_workers, cev().edge_watches - ew0, cev().installs, ri && ri->ref == w.x);
    eval_set_hold(NULL, NULL); eval_release_held(); eval_run();
    stop();
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    const char *m = argc > 1 ? argv[1] : "all";
    if (argc > 2) g_workers = (size_t)strtoull(argv[2], NULL, 10);
    if (argc > 3) g_policy = !strcmp(argv[3], "lifo") ? POL_LIFO : !strcmp(argv[3], "random") ? POL_RANDOM : POL_FIFO;
    bool all = !strcmp(m, "all");
    if (all || !strcmp(m, "pending")) { t_pending(false); t_pending(true); }
    if (all || !strcmp(m, "race-deliver")) t_race_deliver();
    if (all || !strcmp(m, "race-adopt")) { t_pending(false); t_race_adopt_join(); }
    if (all || !strcmp(m, "multi")) t_multi();
    if (all || !strcmp(m, "premise")) t_premise();
    if (all || !strcmp(m, "guards")) t_guards();
    if (all || !strcmp(m, "budget")) t_budget();
    if (all || !strcmp(m, "teardown")) t_teardown();
    if (all || !strcmp(m, "edge")) t_edge();
    printf("test_live_cut %s: %d failures\n", m, fails);
    return fails ? 1 : 0;
}
