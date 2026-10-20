/* test_records.c — stepped interning: records built one word per step in
 * pooled pages and inserted by the stepped state machine agree with the
 * synchronous interner; long shared prefixes; concurrent insertion of the
 * same records by stepped and synchronous inserters yields one id each. */
#include "reading.h"
#include "../src/eval.h"
#include "../src/lib.h"
#include <pthread.h>

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static Interner T;
static uint64_t word_of(uint64_t seed, uint64_t i) { uint64_t x = seed * 0x9E3779B97F4A7C15ULL + i * 0xBF58476D1CE4E5B9ULL; return x ^ (x >> 29); }

/* build(seed, n): push one word per step, then the interning subroutine */
typedef struct { WordBuf b; uint64_t i; bool created; } BuildLoc;
static Family F_BUILD;
static void build_step(Cont *k, uint64_t v) {
    BuildLoc *L = FR_LOC(k, BuildLoc);
    uint64_t id = 0;
    FR_BEGIN(k);
    wordbuf_init(&L->b);
    for (L->i = 0; L->i < k->w[1]; L->i++) { wordbuf_push(&L->b, word_of(k->w[0], L->i)); FR_YIELD(k); }
    FR_CALL(k, id, intern_sub(k, &T, &L->b, &L->created));
    FR_FINISH(k, id * 2 + (L->created ? 1 : 0));
    FR_END(k);
}

#define NREC 600
static uint64_t ids[8][NREC];
static pthread_barrier_t gate;
static uint64_t rec_len(size_t r) { return 1 + (r * 37) % 300; }
static void *racer(void *p) {
    size_t me = *(size_t *)p;
    pthread_barrier_wait(&gate);
    for (size_t q = 0; q < NREC; q++) {
        size_t r = (q * 7 + me * 131) % NREC;      /* different orders per thread */
        size_t n = rec_len(r);
        if (me % 2 == 0) {
            uint64_t *w = malloc(n * sizeof(uint64_t));
            for (size_t i = 0; i < n; i++) w[i] = word_of(r, i);
            ids[me][r] = interner_intern(&T, w, n, NULL);
            free(w);
        } else {
            WordBuf b; wordbuf_init(&b);
            for (size_t i = 0; i < n; i++) wordbuf_push(&b, word_of(r, i));
            InternState s; intern_begin(&s, &T, NULL, &b, n);
            int st; while ((st = intern_advance(&s, 1)) == INTERN_RUNNING) {}
            ids[me][r] = st == INTERN_DONE ? s.result : intern_complete(&s);
        }
    }
    return NULL;
}

int main(void) {
    machine_init();
    F_BUILD = family_new("test.build", build_step, sizeof(BuildLoc));
    interner_init(&T);
    /* agreement with the synchronous interner */
    uint64_t w[10000];
    for (size_t i = 0; i < 10000; i++) w[i] = word_of(5, i);
    size_t s0 = rd(RD_STEPS, F_BUILD), is0 = rd(RD_STEPS, F_INTERN), fs0 = rd(RD_STEPS, F_FLATTEN);
    WhnfStatus st;
    uint64_t r = family_run(F_BUILD, 5, 10000, &st);
    CHECK(st == W_OK && (r & 1) && interner_intern(&T, w, 10000, NULL) == r / 2, "a 10000-word record built and inserted in steps is the synchronous record");
    CHECK(rd(RD_STEPS, F_BUILD) - s0 == 10002, "the builder: one step per word, one call, one finish");
    {   /* units before the root: 667 leaves (⌈10000/15⌉), 44 nodes carried from level 0
         * (667 = 44·15 + 7), 2 from level 1 (44 = 2·15 + 14), and the fold: level 0's 7 → a node
         * carried into level 1 (now 15 → a node), level 2's 2+1 → the top: 667 + 44 + 2 + 3 = 716 */
        size_t units = 0; InternState q; Interner X; interner_init(&X);
        intern_begin(&q, &X, w, NULL, 10000); while (intern_advance(&q, 1) == INTERN_RUNNING) units++;
        interner_free(&X);
        size_t is = rd(RD_STEPS, F_INTERN) - is0, fs = rd(RD_STEPS, F_FLATTEN) - fs0;
        CHECK(units == 716 && is == (units + 1 + 7) / 8 + 1, "the insertion: ⌈units/8⌉ steps, then the flatten request's resumption");
        CHECK(fs == 667 + 2, "the flatten owner: one leaf per step, a start and the publication"); }
    uint64_t again = family_call(F_BUILD, 5, 10000);
    CHECK(again / 2 == r / 2, "the same record from the inline driver");
    uint64_t id7 = interner_intern(&T, w, 7, NULL);
    r = family_run(F_BUILD, 5, 7, &st);
    CHECK(r / 2 == id7 && !(r & 1), "a record inserted synchronously is found by the stepped insertion");
    uint64_t e0 = interner_intern(&T, w, 0, NULL);
    r = family_run(F_BUILD, 999, 0, &st);
    CHECK(r / 2 == e0, "the empty record");
    /* review 5886af7 finding 3: two equal records, serial versus alternating */
    {   size_t tot[2];
        for (int alt = 0; alt < 2; alt++) {
            Interner X; interner_init(&X);
            WordBuf a, b; wordbuf_init(&a); wordbuf_init(&b);
            for (uint64_t i = 0; i < 1000; i++) { wordbuf_push(&a, i); wordbuf_push(&b, i); }
            InternState x, y; intern_begin(&x, &X, NULL, &a, a.n); intern_begin(&y, &X, NULL, &b, b.n);
            int sx = INTERN_RUNNING, sy = INTERN_RUNNING; size_t nx = 0, ny = 0;
            while (sx == INTERN_RUNNING || sy == INTERN_RUNNING) {
                if (sx == INTERN_RUNNING) { sx = intern_advance(&x, 1); nx++; }
                if (sy == INTERN_RUNNING && (alt || sx != INTERN_RUNNING)) { sy = intern_advance(&y, 1); ny++; }
            }
            uint64_t e0 = rd(RD_STEP, 0);
            uint64_t ix = intern_complete(&x), iy = intern_complete(&y);
            uint64_t e1 = rd(RD_STEP, 0);
            tot[alt] = nx + ny + (e1 - e0);
            CHECK(ix == iy && x.created != y.created, alt ? "alternating: one record, one creator of its tree" : "serial: one record, one creator of its tree");
            interner_free(&X);
        }
        CHECK(tot[0] == tot[1], "equal records: the same counted work serially and alternated"); }
    /* long shared prefixes: records differing only in their last word */
    bool distinct = true, found = true;
    uint64_t pid[40];
    for (size_t q = 0; q < 40; q++) {
        w[2999] = q;
        if (q % 2) pid[q] = interner_intern(&T, w, 3000, NULL);
        else {
            WordBuf b; wordbuf_init(&b);
            for (size_t i = 0; i < 3000; i++) wordbuf_push(&b, w[i]);
            InternState s; intern_begin(&s, &T, NULL, &b, 3000);
            int st; while ((st = intern_advance(&s, 3)) == INTERN_RUNNING) {}
            pid[q] = st == INTERN_DONE ? s.result : intern_complete(&s);
        }
        for (size_t p = 0; p < q; p++) if (pid[p] == pid[q]) distinct = false;
    }
    for (size_t q = 0; q < 40; q++) { w[2999] = q; if (interner_find(&T, w, 3000) != pid[q]) found = false; }
    CHECK(distinct && found, "forty records sharing a 2999-word prefix: distinct ids, each found");
    interner_free(&T);
    /* concurrent insertion of the same records */
    interner_init(&T);
    pthread_barrier_init(&gate, NULL, 8);
    pthread_t th[8]; size_t me[8];
    for (size_t i = 0; i < 8; i++) { me[i] = i; pthread_create(&th[i], NULL, racer, &me[i]); }
    for (size_t i = 0; i < 8; i++) pthread_join(th[i], NULL);
    pthread_barrier_destroy(&gate);
    bool agree = true, live = true;
    for (size_t q = 0; q < NREC; q++) {
        for (size_t i = 1; i < 8; i++) if (ids[i][q] != ids[0][q]) agree = false;
        if (!interner_live(&T, ids[0][q])) live = false;
    }
    size_t nlive = 0; for (size_t id = 1; id <= interner_count(&T); id++) if (interner_live(&T, id)) nlive++;
    CHECK(agree && live && nlive == NREC, "eight stepped and synchronous inserters: one published id per record");
    bool ok = true;
    for (size_t q = 0; q < NREC && ok; q++) {
        size_t n = rec_len(q); size_t m; const uint64_t *x = interner_get(&T, ids[0][q], &m);
        if (m != n) ok = false;
        for (size_t i = 0; i < n && ok; i++) if (x[i] != word_of(q, i)) ok = false;
    }
    CHECK(ok, "every published record holds its words");
    interner_free(&T);
    /* the stable store covers every size_t index: sparse indices past 2^26,
     * across radix boundaries and at SIZE_MAX keep their addresses and values,
     * and create nothing in between */
    {   Chunked c; chunked_init(&c, sizeof(uint64_t));
        size_t at[6] = { 0, 5, ((size_t)1 << 26) + 7, ((size_t)1 << 37) + 3, ((size_t)1 << 48) + 11, SIZE_MAX };
        uint64_t *p0 = chunked_at(&c, 0); *p0 = 100;
        bool keep = true;
        for (size_t q = 1; q < 6; q++) { *(uint64_t *)chunked_at(&c, at[q]) = 100 + q; if (chunked_at(&c, 0) != p0) keep = false; }
        for (size_t q = 0; q < 6; q++) if (*(uint64_t *)chunked_get(&c, at[q]) != 100 + q) keep = false;
        CHECK(keep, "sparse indices up to SIZE_MAX keep their addresses and values");
        CHECK(!chunked_peek(&c, (size_t)1 << 30) && !chunked_peek(&c, SIZE_MAX - CHUNK_SIZE), "no intervening element exists");
        chunked_free(&c); }
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}
