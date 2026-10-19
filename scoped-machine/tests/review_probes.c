/* review_probes.c — the staged overlaps of review 5886af7 as permanent
 * regressions. The gates only pause between existing production
 * instructions (linker wraps of interner_intern and whnf_pinned); they change
 * no rule.
 *
 *   duplicate  two root clients of one fresh key: one body, two deliveries
 *   handoff    a frame handed to the queue is never touched by its former
 *              owner: later frames do not alias
 *   refpub     a reference's record is discoverable before its side data:
 *              a concurrent requester waits for the complete reference
 *   revision   a body published between a checked observation's premises and
 *              its evaluation is not unfolded by that observation
 */
#include "../src/compiler.h"
#include "../src/check.h"
#include <stdatomic.h>
#include <sched.h>

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

/* ---- duplicate ---- */
static Family F;
static atomic_int bodies;
static EntryId probe_entry(void) { EntryId e = 0; for (EntryId i = 1; i <= eval_entry_count(); i++) if (eval_entry_live(i) && eval_entry_family(i) == F) e = i; return e; }
static void duplicate_step(Cont *k, uint64_t v) {
    (void)v;
    atomic_fetch_add(&bodies, 1);
    /* hold the body until the second client has requested the key */
    for (;;) { size_t rq, dl, pb; eval_entry_events(probe_entry(), &rq, &dl, &pb); if (rq >= 2) break; sched_yield(); }
    frame_finish(k, 42);
}
static void *caller(void *p) { *(uint64_t *)p = family_call(F, 7, 0); return NULL; }

/* ---- handoff ---- */
static atomic_int release_first;
static void handoff_step(Cont *k, uint64_t v) {
    (void)v;
    if (!k->pc) {
        k->pc = 1;
        frame_yield(k);
        while (!atomic_load(&release_first)) sched_yield();   /* preemption after queue publication */
        return;
    }
    frame_finish(k, 42);
}

/* ---- refpub ---- */
static TermVarId pub_x; static atomic_int pub_armed, pub_paused;
uint64_t __real_interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created);
uint64_t __wrap_interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    uint64_t id = __real_interner_intern(t, w, n, created);
    if (atomic_load(&pub_armed) && t == &M.refs && n == 2 && w[0] == 1 && w[1] == pub_x) {
        atomic_store(&pub_armed, 0);
        atomic_store(&pub_paused, 1);
        /* the record is discoverable; its side data is not written yet: wait
         * until the second requester is a waiter of the producer's key */
        Family fv = family_lookup("ref.var");
        for (;;) {
            size_t rq = 0, dl, pb;
            for (EntryId i = 1; i <= eval_entry_count(); i++) if (eval_entry_live(i) && eval_entry_family(i) == fv && eval_entry_a(i) == pub_x) eval_entry_events(i, &rq, &dl, &pb);
            if (rq >= 2) break;
            sched_yield();
        }
    }
    return id;
}
static RefId pub_got[2];
static void *pub_client(void *p) {
    size_t i = *(size_t *)p;
    if (i == 1) while (!atomic_load(&pub_paused)) sched_yield();
    pub_got[i] = ref_var(pub_x);
    return NULL;
}

/* ---- revision ---- */
static RefId rv_target, rv_bad; static SymbolId rv_symbol; static int rv_armed;
EvalResult *__real_whnf_pinned(RefId, FaceId, uint64_t, WhnfStatus *);
EvalResult *__wrap_whnf_pinned(RefId t, FaceId face, uint64_t pins, WhnfStatus *status) {
    if (rv_armed && t == rv_target) { rv_armed = 0; require(set_global_body(rv_symbol, rv_bad), "body publication failed"); }
    return __real_whnf_pinned(t, face, pins, status);
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "duplicate";
    machine_init(); eval_init(); check_init();
    if (!strcmp(mode, "duplicate")) {
        F = family_define("probe.duplicate", duplicate_step, 0, true);
        eval_set_workers(2);
        pthread_t a, b; uint64_t x = 0, y = 0;
        pthread_create(&a, NULL, caller, &x);
        while (atomic_load(&bodies) != 1) sched_yield();
        pthread_create(&b, NULL, caller, &y);
        pthread_join(a, NULL); pthread_join(b, NULL);
        EntryId e = probe_entry(); size_t rq, dl, pb; eval_entry_events(e, &rq, &dl, &pb);
        CHECK(x == 42 && y == 42, "both clients receive the value");
        CHECK(atomic_load(&bodies) == 1 && eval_entry_runs(e) == 1 && family_steps(F) == 1, "one body: the second client attaches to the running producer");
        CHECK(rq == 2 && dl == 2 && pb == 1, "two requests, two deliveries, one publication");
        eval_set_workers(0);
    } else if (!strcmp(mode, "handoff")) {
        F = family_define("probe.handoff", handoff_step, 0, true);
        eval_set_workers(2);
        WhnfStatus st; uint64_t v = family_run(F, 7, 0, &st);
        atomic_store(&release_first, 1);
        eval_run(); eval_set_workers(0);
        Cont *a = frame_new(F, 0), *b = frame_new(F, 0), *c = frame_new(F, 0);
        CHECK(v == 42 && st == W_OK && a != b && a != c && b != c, "a handed-off frame is not released twice (no aliasing)");
    } else if (!strcmp(mode, "refpub")) {
        RefId U = mk_universe(0);
        pub_x = declare_term(U, fc_true());
        eval_set_workers(2);
        atomic_store(&pub_armed, 1);
        pthread_t th[2]; size_t ids[2] = { 0, 1 };
        for (int i = 0; i < 2; i++) pthread_create(&th[i], NULL, pub_client, &ids[i]);
        for (int i = 0; i < 2; i++) pthread_join(th[i], NULL);
        eval_set_workers(0);
        size_t n; const uint64_t *fv = varset_get(ref_freevars(pub_got[1]), &n);
        CHECK(pub_got[0] == pub_got[1] && pub_got[0] != 0, "one reference for both requesters");
        CHECK(n >= 1 && fv[0] == pub_x && ref_required(pub_got[1]) != 0, "the second requester received the complete reference (side data written)");
    } else if (!strcmp(mode, "revision")) {
        RefId U = mk_universe(0);
        TermVarId a = declare_term(U, fc_true()); RefId A = ref_var(a);
        TermVarId x = declare_term(A, fc_true()); RefId X = ref_var(x);
        CtxDecl ds[2] = { { S_TERM, a, U }, { S_TERM, x, A } };
        ContextId G = context_make(2, ds, fc_true());
        uint64_t ps[2] = { a, x };
        rv_symbol = define_global("publication-between-check-and-observation", varset_make(ps, 2), dimset_make(NULL, 0), A);
        rv_target = global_ref(rv_symbol); rv_bad = mk_pair(X, X);
        const char *why = ""; WhnfStatus status;
        rv_armed = 1;
        EvalResult *r = observe_checked(G, rv_target, &status, &why);
        CheckStatus later = check(G, fc_true(), rv_target, A, &why);
        CHECK(!rv_armed, "the interleaving was staged");
        CHECK(status == W_OK && r && r->cls == R_NEUTRAL, "the observation stays at the opaque revision its premises validated");
        CHECK(later == CK_INVALID, "a new request reads the new body and rejects it");
    } else die("unknown mode %s", mode);
    check_free(); eval_free(); machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}
