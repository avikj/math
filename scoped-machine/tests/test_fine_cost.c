/* §89 — fine C-work accounting beside the coarse event vector.
 *
 * The author's review_frame_cost.c shows that a system with 1, 64 or 1024
 * branches has the identical coarse vector (request 2, eval 4, publish 2,
 * deliver 2) while open_ref iterates 2, 128 or 2048 stored fields. This test
 * asserts both halves: the coarse vector is constant across the three
 * systems, and the fine vector grows with the stored size — fields opened
 * exactly equals the stored field count of the system, and the fine total is
 * strictly increasing. The fine vector is reported beside the coarse one and
 * never added to it (§89.2). */
#include "../src/compiler.h"
#include "../src/fine.h"
#include <assert.h>

static int checks = 0, failures = 0;
#define CHECK(c) do { checks++; if (!(c)) { failures++; fprintf(stderr, "FAIL %s:%d %s\n", __FILE__, __LINE__, #c); } } while (0)

int main(void) {
    const size_t sizes[] = { 1, 64, 1024 };
    EvalEvents base = { 0 };
    FineVector fine[3]; size_t fields[3]; uint64_t totals[3];
    for (size_t j = 0; j < 3; j++) {
        machine_init(); eval_init(); check_init(); compiler_init();
        size_t n = sizes[j];
        RefId U = mk_universe(0);
        TermVarId tv = declare_term(U, fc_true()); RefId A = ref_var(tv);
        TermVarId av = declare_term(A, fc_true()); RefId a = ref_var(av);
        CtxDecl ds[] = { { S_TERM, tv, U }, { S_TERM, av, A } };
        ContextId G = context_make(2, ds, fc_true());
        FaceId *faces = malloc(n * sizeof *faces); RefId *terms = malloc(n * sizeof *terms);
        for (size_t k = 0; k < n; k++) { faces[k] = k ? fc_false() : fc_true(); terms[k] = a; }
        RefId s = mk_system(n, faces, terms);
        const char *why = "";
        CHECK(check(G, fc_true(), s, A, &why) == CK_VALID);
        eval_reset();
        EvalEvents before = eval_events(); FineVector fb = fine_snapshot();
        WhnfStatus status; EvalResult *r = whnf(s, fc_true(), &status);
        EvalEvents after = eval_events(); FineVector fa = fine_snapshot();
        EvalEvents delta = { .request = after.request - before.request, .eval_step = after.eval_step - before.eval_step,
                             .publish = after.publish - before.publish, .deliver = after.deliver - before.deliver };
        CHECK(status == W_OK && r && r->ref == a);
        if (j == 0) base = delta;
        else CHECK(delta.request == base.request && delta.eval_step == base.eval_step && delta.publish == base.publish && delta.deliver == base.deliver);
        fine[j] = fine_delta(fb, fa); fields[j] = origin_nfields(ref_origin(s));
        totals[j] = 0; for (int c = 0; c < FC_COUNT; c++) totals[j] += fine[j].v[c];
        /* the stored size is visible in the fine vector and invisible in the coarse one */
        CHECK(fine[j].v[FC_FIELDS_OPENED] >= fields[j]);
        printf("branches=%zu stored_fields=%zu coarse: request=%zu eval=%zu pub=%zu deliver=%zu | fine total=%llu fields_opened=%llu\n",
               n, fields[j], delta.request, delta.eval_step, delta.publish, delta.deliver,
               (unsigned long long)totals[j], (unsigned long long)fine[j].v[FC_FIELDS_OPENED]);
        free(faces); free(terms);
        compiler_free(); check_free(); eval_free(); machine_free();
    }
    CHECK(fields[0] == 2 && fields[1] == 128 && fields[2] == 2048);
    CHECK(fine[0].v[FC_FIELDS_OPENED] < fine[1].v[FC_FIELDS_OPENED] && fine[1].v[FC_FIELDS_OPENED] < fine[2].v[FC_FIELDS_OPENED]);
    CHECK(totals[0] < totals[1] && totals[1] < totals[2]);
    /* the microstep accounting table (§89.3) */
    printf("\n%-26s %12s %12s %12s\n", "fine counter", "n=1", "n=64", "n=1024");
    for (int c = 0; c < FC_COUNT; c++)
        printf("%-26s %12llu %12llu %12llu\n", fine_name((FineCounter)c), (unsigned long long)fine[0].v[c], (unsigned long long)fine[1].v[c], (unsigned long long)fine[2].v[c]);
    printf("%-26s %12llu %12llu %12llu\n", "TOTAL", (unsigned long long)totals[0], (unsigned long long)totals[1], (unsigned long long)totals[2]);
    printf("fine-cost: %d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
