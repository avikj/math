#include "eval.h"
#include "lib.h"

/* ---------------- continuations and tasks ---------------- */

typedef enum {
    K_ROOT = 1, K_FORWARD, K_APP, K_FST, K_SND, K_PAPP, K_UNGLUE, K_COMP_FAMILY, K_BRANCH, K_EXTERNAL
} ContKind;

/* branchwise evaluation of a guarded system: one continuation per branch,
 * the guarded results are gathered and published together */
typedef struct {
    EntryId dest;
    size_t n, arrived;
    FaceId *faces;
    EvalResult **results;
    bool failed;
} Gather;

struct Cont {
    ContKind kind;
    EntryId dest;       /* entry to publish into (not for ROOT/EXTERNAL) */
    FaceId chi;         /* ambient face of the demanding evaluation */
    RefId orig;         /* the eliminator / composition reference, retained */
    RefId a;            /* APP argument */
    IntervalId s;       /* PAPP interval */
    DimVarId j;         /* COMP: the symbolic dimension */
    RefId tube;         /* COMP: tube body at j */
    FaceId phi;         /* COMP: tube face */
    RefId cap;          /* COMP: cap */
    /* BRANCH */
    Gather *gather;
    size_t branch;
    /* ROOT */
    EvalResult **root_out;
    bool *root_done;
    /* EXTERNAL */
    ExternalDeliver ext_fn;
    void *ext_ctx;
};

typedef struct { bool is_resume; EntryId entry; Cont *k; EvalResult *r; } Task;

static struct {
    Interner keys;                 /* (ref, face) → EntryId */
    Entry *entries; size_t n_entries, cap_entries;
    VEC(Task) queue; size_t qhead;
    VEC(Cont *) conts;             /* all allocated continuations (rooted) */
    VEC(EvalResult *) results;     /* all allocated results (rooted) */
    VEC(Gather *) gathers;
    size_t tasks_created;
    EvalEvents ev;
    SchedPolicy policy; uint64_t rng;
} E;

EvalEvents eval_events(void) { return E.ev; }
void eval_set_policy(SchedPolicy p, uint64_t seed) { E.policy = p; E.rng = seed ? seed : 0x9E3779B97F4A7C15ULL; }
static uint64_t rng_next(void) { E.rng ^= E.rng << 13; E.rng ^= E.rng >> 7; E.rng ^= E.rng << 17; return E.rng; }

void eval_init(void) {
    memset(&E, 0, sizeof E);
    interner_init(&E.keys);
}

void eval_free(void) {
    interner_free(&E.keys);
    for (size_t i = 0; i < E.n_entries; i++) vec_free(&E.entries[i].waiters);
    free(E.entries);
    for (size_t i = 0; i < E.conts.len; i++) free(E.conts.data[i]);
    vec_free(&E.conts);
    for (size_t i = 0; i < E.results.len; i++) { free(E.results.data[i]->faces); free(E.results.data[i]->terms); free(E.results.data[i]); }
    vec_free(&E.results);
    for (size_t i = 0; i < E.gathers.len; i++) { free(E.gathers.data[i]->faces); free(E.gathers.data[i]->results); free(E.gathers.data[i]); }
    vec_free(&E.gathers);
    vec_free(&E.queue);
    memset(&E, 0, sizeof E);
}

static Cont *cont_new(ContKind kind, EntryId dest, FaceId chi) {
    Cont *k = calloc(1, sizeof *k);
    require(k, "out of memory");
    k->kind = kind; k->dest = dest; k->chi = chi;
    vec_push(&E.conts, k);
    return k;
}

Cont *cont_external(ExternalDeliver fn, void *ctx) {
    Cont *k = cont_new(K_EXTERNAL, 0, 0);
    k->ext_fn = fn; k->ext_ctx = ctx;
    return k;
}

static EvalResult *result_new(ResultClass cls, RefId ref) {
    EvalResult *r = calloc(1, sizeof *r);
    require(r, "out of memory");
    r->cls = cls; r->ref = ref;
    vec_push(&E.results, r);
    return r;
}

static EvalResult *result_invalid(const char *msg) {
    EvalResult *r = result_new(R_INVALID, 0);
    r->message = msg;
    return r;
}

static EvalResult *result_system(RefId owner, size_t n, const FaceId *faces, const RefId *terms) {
    EvalResult *r = result_new(R_SYSTEM, owner);
    r->nbr = n;
    r->faces = malloc((n ? n : 1) * sizeof(FaceId));
    r->terms = malloc((n ? n : 1) * sizeof(RefId));
    require(r->faces && r->terms, "out of memory");
    if (n) { memcpy(r->faces, faces, n * sizeof(FaceId)); memcpy(r->terms, terms, n * sizeof(RefId)); }
    return r;
}

static void enqueue_evaluate(EntryId e) {
    Task t = { false, e, NULL, NULL };
    vec_push(&E.queue, t);
    E.tasks_created++;
}
static void enqueue_resume(Cont *k, EvalResult *r) {
    Task t = { true, 0, k, r };
    vec_push(&E.queue, t);
}

/* ---------------- entries ---------------- */

static EntryId entry_intern(RefId t, FaceId eta) {
    uint64_t w[2] = { t, eta };
    bool created;
    EntryId id = interner_intern(&E.keys, w, 2, &created);
    if (created) {
        if (id > E.cap_entries) {
            size_t nc = E.cap_entries ? E.cap_entries * 2 : 64;
            while (nc < id) nc *= 2;
            E.entries = realloc(E.entries, nc * sizeof(Entry));
            require(E.entries, "out of memory");
            E.cap_entries = nc;
        }
        Entry *e = &E.entries[id - 1];
        memset(e, 0, sizeof *e);
        e->ref = t; e->face = eta; e->state = E_UNEVALUATED;
        E.n_entries = id;
    }
    return id;
}

EntryId eval_entry_lookup(RefId t, FaceId chi) {
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    uint64_t w[2] = { t, fc_project(chi, S, n) };
    return interner_find(&E.keys, w, 2);
}
EntryState eval_entry_state(EntryId e) { return E.entries[e - 1].state; }
FaceId eval_entry_face(EntryId e) { return E.entries[e - 1].face; }
size_t eval_entry_count(void) { return E.n_entries; }
size_t eval_entry_runs(EntryId e) { return E.entries[e - 1].runs; }
RefId eval_entry_ref(EntryId e) { return E.entries[e - 1].ref; }
void eval_entry_events(EntryId e, size_t *req, size_t *deliver, size_t *pub) { *req = E.entries[e - 1].n_req; *deliver = E.entries[e - 1].n_deliver; *pub = E.entries[e - 1].n_pub; }
size_t eval_running_count(void) { size_t c = 0; for (size_t i = 0; i < E.n_entries; i++) if (E.entries[i].state == E_RUNNING) c++; return c; }
size_t eval_task_count(void) { return E.tasks_created; }

/* DELIVER is counted here, on the common delivery path, for ready hits and
 * for publication alike; the resumed frame step is counted in eval_run as an
 * EVAL_STEP when the RESUME job executes. */
static void deliver(Cont *k, EvalResult *r) { E.ev.deliver++; enqueue_resume(k, r); }
static void deliver_from(EntryId eid, Cont *k, EvalResult *r) { E.entries[eid - 1].n_deliver++; deliver(k, r); }

static void publish(EntryId eid, EvalResult *r) {
    Entry *e = &E.entries[eid - 1];
    require(e->state == E_RUNNING, "publish into an entry that is not running");
    require(r->cls != R_NO_OBSERVATION, "no observation is never a published value");
    E.ev.publish++; e->n_pub++;
    e->result = r;
    e->state = E_READY;
    /* detach all waiters, then deliver */
    Cont **ws = e->waiters.data; size_t n = e->waiters.len;
    e->waiters.data = NULL; e->waiters.len = e->waiters.cap = 0;
    for (size_t i = 0; i < n; i++) deliver_from(eid, ws[i], r);
    free(ws);
}

static bool validate_occurrence(RefId t, FaceId chi) {
    /* the ambient face must entail the reference's required face (which
     * already folds in the required faces of its free variables) */
    return fc_entails(chi, ref_required(t));
}

void eval_request(RefId t, FaceId chi, Cont *k) {
    if (fc_is_false(chi)) { deliver(k, result_new(R_NO_OBSERVATION, t)); return; }
    if (!validate_occurrence(t, chi)) { deliver(k, result_invalid("occurrence outside its required face")); return; }
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    FaceId eta = fc_project(chi, S, n);
    EntryId eid = entry_intern(t, eta);
    Entry *e = &E.entries[eid - 1];
    E.ev.request++; e->n_req++;
    if (e->state == E_READY) { E.ev.ready_hit++; deliver_from(eid, k, e->result); return; }
    if (e->state == E_RUNNING) { E.ev.running_hit++; vec_push(&e->waiters, k); return; }
    E.ev.launch++;
    e->state = E_RUNNING;
    vec_push(&e->waiters, k);
    enqueue_evaluate(eid);
}

static void forward(RefId t, FaceId chi, EntryId dest) { eval_request(t, chi, cont_new(K_FORWARD, dest, chi)); }

/* ---------------- dispatch ---------------- */

static void eval_system_head(RefId t, const Head *h, FaceId chi, EntryId dest) {
    size_t nb = h->n / 2;
    FaceId *faces = malloc((nb ? nb : 1) * sizeof(FaceId));
    RefId *terms = malloc((nb ? nb : 1) * sizeof(RefId));
    require(faces && terms, "out of memory");
    size_t kept = 0;
    FaceId uni = fc_false();
    for (size_t k = 0; k < nb; k++) {
        FaceId phi = h->f[2 * k].id;
        RefId tk = h->f[2 * k + 1].id;
        if (fc_is_false(fc_meet(chi, phi))) continue;           /* inconsistent branch dropped */
        if (fc_entails(chi, phi)) { free(faces); free(terms); forward(tk, chi, dest); return; }
        faces[kept] = phi; terms[kept] = tk; kept++;
        uni = fc_join(uni, phi);
    }
    if (!fc_entails(chi, uni)) { free(faces); free(terms); publish(dest, result_invalid("system does not cover the ambient face")); return; }
    publish(dest, result_system(t, kept, faces, terms));
    free(faces); free(terms);
}

static void evaluate(EntryId eid) {
    Entry *e = &E.entries[eid - 1];
    require(e->state == E_RUNNING && e->runs == 0, "a key is evaluated by exactly one task");
    e->runs++;
    RefId t = e->ref;
    FaceId chi = e->face;      /* evaluate under the key's face, not a requester's */
    if (ref_is_var(t)) { publish(eid, result_new(R_NEUTRAL, t)); return; }
    Head h; open_ref(t, &h);
    switch (h.tag) {
    case T_UNIVERSE: case T_PI: case T_SIGMA: case T_LAM: case T_PAIR: case T_PATH: case T_PLAM:
        publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_GLOBAL:
        forward(unfold_global(t), chi, eid);
        break;
    case T_APP: {
        Cont *k = cont_new(K_APP, eid, chi); k->orig = t; k->a = h.f[1].id;
        eval_request(h.f[0].id, chi, k);
        break;
    }
    case T_FST: case T_SND: {
        Cont *k = cont_new(h.tag == T_FST ? K_FST : K_SND, eid, chi); k->orig = t;
        eval_request(h.f[0].id, chi, k);
        break;
    }
    case T_PAPP: {
        IntervalId s = h.f[4].id;
        if (fc_entails(chi, fc_endpoint(s, 0))) { forward(h.f[1].id, chi, eid); break; }
        if (fc_entails(chi, fc_endpoint(s, 1))) { forward(h.f[2].id, chi, eid); break; }
        Cont *k = cont_new(K_PAPP, eid, chi); k->orig = t; k->s = s;
        eval_request(h.f[3].id, chi, k);
        break;
    }
    case T_GLUE_TYPE:
        if (fc_entails(chi, h.f[1].id)) forward(h.f[2].id, chi, eid);
        else publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_GLUE_INTRO:
        if (fc_entails(chi, h.f[1].id)) forward(h.f[4].id, chi, eid);
        else publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_UNGLUE:
        if (fc_entails(chi, h.f[1].id)) forward(mk_app(mk_fst(h.f[3].id), h.f[4].id), chi, eid);
        else { Cont *k = cont_new(K_UNGLUE, eid, chi); k->orig = t; eval_request(h.f[4].id, chi, k); }
        break;
    case T_SYSTEM:
        eval_system_head(t, &h, chi, eid);
        break;
    case T_COMP: {
        FaceId phi = h.f[1].id;
        if (fc_entails(chi, phi)) {            /* tube coverage first */
            forward(apply_dim_binder(t, 0, 2, iv_one()), chi, eid);
            break;
        }
        DimOpen fam = resolve_dim_binder(t, 0, 0);
        DimOpen tube = resolve_dim_binder(t, 0, 2);
        require(fam.j == tube.j, "family and tube must share the composition dimension");
        Cont *k = cont_new(K_COMP_FAMILY, eid, chi);
        k->orig = t; k->j = fam.j; k->tube = tube.body; k->phi = phi; k->cap = h.f[3].id;
        eval_request(fam.body, chi, k);
        break;
    }
    }
    head_free(&h);
}

/* rebuild an eliminator around a new scrutinee (system distribution) */
static RefId rebuild_elim(const Cont *k, RefId scrut) {
    Head h; open_ref(k->orig, &h);
    RefId out = 0;
    switch (k->kind) {
    case K_APP: out = mk_app(scrut, h.f[1].id); break;
    case K_FST: out = mk_fst(scrut); break;
    case K_SND: out = mk_snd(scrut); break;
    case K_PAPP: {
        DimOpen B = resolve_dim_binder(k->orig, 0, 0);
        out = mk_papp(B.j, B.body, h.f[1].id, h.f[2].id, scrut, h.f[4].id);
        break;
    }
    case K_UNGLUE: out = mk_unglue(h.f[0].id, h.f[1].id, h.f[2].id, h.f[3].id, scrut); break;
    default: die("rebuild of a non-eliminator");
    }
    head_free(&h);
    return out;
}

/* Act branchwise: demand each guarded term under chi ∧ phi_k, then publish
 * the reconstructed guarded result (§12). */
static void publish_branchwise(EntryId dest, FaceId chi, size_t n, const FaceId *faces, const RefId *terms) {
    Gather *g = calloc(1, sizeof *g);
    require(g, "out of memory");
    g->dest = dest; g->n = n;
    g->faces = malloc((n ? n : 1) * sizeof(FaceId));
    g->results = calloc(n ? n : 1, sizeof(EvalResult *));
    require(g->faces && g->results, "out of memory");
    if (n) memcpy(g->faces, faces, n * sizeof(FaceId));
    vec_push(&E.gathers, g);
    for (size_t i = 0; i < n; i++) {
        Cont *k = cont_new(K_BRANCH, dest, fc_meet(chi, faces[i]));
        k->gather = g; k->branch = i; k->orig = terms[i];
        eval_request(terms[i], k->chi, k);
    }
}

static void resume_branch(Cont *k, EvalResult *r) {
    Gather *g = k->gather;
    g->results[k->branch] = r;
    if (r->cls == R_INVALID || r->cls == R_NO_OBSERVATION) g->failed = true;
    if (++g->arrived < g->n) return;           /* the join is enabled only when every box is full */
    if (g->failed) {
        /* report the first failing branch in branch order, independent of arrival order */
        for (size_t i = 0; i < g->n; i++) {
            EvalResult *b = g->results[i];
            if (b->cls == R_INVALID) { publish(g->dest, b); return; }
            if (b->cls == R_NO_OBSERVATION) { publish(g->dest, result_invalid("branch under an inconsistent guard")); return; }
        }
    }
    /* reconstruct: nested system results are flattened under conjoined guards */
    Words fs, ts; words_init(&fs); words_init(&ts);
    for (size_t i = 0; i < g->n; i++) {
        EvalResult *b = g->results[i];
        if (b->cls == R_SYSTEM) {
            for (size_t j = 0; j < b->nbr; j++) { words_push(&fs, fc_meet(g->faces[i], b->faces[j])); words_push(&ts, b->terms[j]); }
        } else { words_push(&fs, g->faces[i]); words_push(&ts, b->ref); }
    }
    RefId owner = mk_system(fs.n, fs.w, ts.w);
    publish(g->dest, result_system(owner, fs.n, fs.w, ts.w));
    words_free(&fs); words_free(&ts);
}

static void distribute(const Cont *k, const EvalResult *sys) {
    RefId *terms = malloc((sys->nbr ? sys->nbr : 1) * sizeof(RefId));
    require(terms, "out of memory");
    for (size_t i = 0; i < sys->nbr; i++) terms[i] = rebuild_elim(k, sys->terms[i]);
    publish_branchwise(k->dest, k->chi, sys->nbr, sys->faces, terms);
    free(terms);
}

static void resume_comp_family(Cont *k, EvalResult *r) {
    if (r->cls == R_NEUTRAL) { publish(k->dest, result_new(R_NEUTRAL, k->orig)); return; }
    if (r->cls == R_SYSTEM) {
        /* branch available along the whole j line: outer guard ∀j.phi_k */
        FaceId *faces = malloc((r->nbr ? r->nbr : 1) * sizeof(FaceId));
        RefId *terms = malloc((r->nbr ? r->nbr : 1) * sizeof(RefId));
        require(faces && terms, "out of memory");
        size_t kept = 0; FaceId uni = fc_false();
        for (size_t i = 0; i < r->nbr; i++) {
            FaceId g = fc_forall(k->j, r->faces[i]);
            if (fc_is_false(fc_meet(k->chi, g))) continue;
            faces[kept] = g;
            terms[kept] = mk_comp(k->j, r->terms[i], k->phi, k->tube, k->cap);
            kept++;
            uni = fc_join(uni, g);
        }
        if (!fc_entails(k->chi, uni)) { free(faces); free(terms); publish(k->dest, result_invalid("type-family system has no branch along the whole composition line")); return; }
        for (size_t i = 0; i < kept; i++) if (fc_entails(k->chi, faces[i])) { RefId ti = terms[i]; free(faces); free(terms); forward(ti, k->chi, k->dest); return; }
        publish_branchwise(k->dest, k->chi, kept, faces, terms);
        free(faces); free(terms);
        return;
    }
    /* introduction: dispatch on the exposed family head */
    Head h; open_ref(r->ref, &h);
    Tag tag = h.tag; head_free(&h);
    RefId out;
    switch (tag) {
    case T_PI: out = comp_clause_pi(k->j, r->ref, k->phi, k->tube, k->cap); break;
    case T_SIGMA: out = comp_clause_sigma(k->j, r->ref, k->phi, k->tube, k->cap); break;
    case T_PATH: out = comp_clause_path(k->j, r->ref, k->phi, k->tube, k->cap); break;
    case T_GLUE_TYPE: out = comp_clause_glue(k->j, r->ref, k->phi, k->tube, k->cap); break;
    case T_UNIVERSE: out = comp_clause_universe(k->j, r->ref, k->phi, k->tube, k->cap); break;
    default: publish(k->dest, result_invalid("composition in a family whose head is not a type former")); return;
    }
    forward(out, k->chi, k->dest);
}

static void resume(Cont *k, EvalResult *r) {
    switch (k->kind) {
    case K_ROOT: *k->root_out = r; *k->root_done = true; return;
    case K_EXTERNAL: k->ext_fn(k->ext_ctx, r); return;
    case K_BRANCH: resume_branch(k, r); return;
    default: break;
    }
    if (r->cls == R_NO_OBSERVATION || r->cls == R_INVALID) { publish(k->dest, r); return; }
    if (k->kind == K_FORWARD) { publish(k->dest, r); return; }
    if (k->kind == K_COMP_FAMILY) { resume_comp_family(k, r); return; }
    if (r->cls == R_NEUTRAL) { publish(k->dest, result_new(R_NEUTRAL, k->orig)); return; }
    if (r->cls == R_SYSTEM) { distribute(k, r); return; }
    /* introduction under an eliminator */
    Head h; open_ref(r->ref, &h);
    switch (k->kind) {
    case K_APP:
        if (h.tag != T_LAM) { publish(k->dest, result_invalid("application of a non-function introduction")); break; }
        forward(apply_term_binder(r->ref, 0, 1, k->a), k->chi, k->dest);
        break;
    case K_FST: case K_SND:
        if (h.tag != T_PAIR) { publish(k->dest, result_invalid("projection of a non-pair introduction")); break; }
        forward(h.f[k->kind == K_FST ? 0 : 1].id, k->chi, k->dest);
        break;
    case K_PAPP:
        if (h.tag != T_PLAM) { publish(k->dest, result_invalid("path application of a non-path introduction")); break; }
        forward(apply_dim_binder(r->ref, 0, 0, k->s), k->chi, k->dest);
        break;
    case K_UNGLUE:
        if (h.tag != T_GLUE_INTRO) { publish(k->dest, result_invalid("unglue of a non-glue introduction")); break; }
        forward(h.f[5].id, k->chi, k->dest);
        break;
    default: die("unreachable continuation kind");
    }
    head_free(&h);
}

size_t eval_run(void) {
    size_t n = 0;
    while (E.qhead < E.queue.len) {
        /* the ready jobs form a multiset; the policy only picks which one runs next */
        size_t pick = E.qhead;
        if (E.policy == SCHED_LIFO) pick = E.queue.len - 1;
        else if (E.policy == SCHED_RANDOM) pick = E.qhead + (size_t)(rng_next() % (E.queue.len - E.qhead));
        Task t = E.queue.data[pick];
        E.queue.data[pick] = E.queue.data[E.qhead];
        E.qhead++;
        E.ev.eval_step++;
        if (t.is_resume) resume(t.k, t.r); else evaluate(t.entry);
        n++;
    }
    E.queue.len = 0; E.qhead = 0;
    return n;
}
static void run(void) { eval_run(); }

EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status) {
    EvalResult *out = NULL; bool done = false;
    Cont *root = cont_new(K_ROOT, 0, chi);
    root->root_out = &out; root->root_done = &done;
    eval_request(t, chi, root);
    run();
    if (!done) { if (status) *status = W_STUCK; return NULL; }
    if (status) {
        if (out->cls == R_NO_OBSERVATION) *status = W_NO_OBSERVATION;
        else if (out->cls == R_INVALID) *status = W_INVALID;
        else *status = W_OK;
    }
    return out;
}

void print_result(const EvalResult *r, FILE *f) {
    if (!r) { fprintf(f, "<pending>"); return; }
    switch (r->cls) {
    case R_INTRODUCTION: fprintf(f, "INTRO "); print_ref(r->ref, f); break;
    case R_NEUTRAL: fprintf(f, "NEUTRAL "); print_ref(r->ref, f); break;
    case R_SYSTEM:
        fprintf(f, "SYSTEM [");
        for (size_t i = 0; i < r->nbr; i++) { if (i) fprintf(f, ", "); fc_print(r->faces[i], f); fprintf(f, " ↦ "); print_ref(r->terms[i], f); }
        fprintf(f, "]");
        break;
    case R_NO_OBSERVATION: fprintf(f, "NO_OBSERVATION"); break;
    case R_INVALID: fprintf(f, "INVALID(%s)", r->message ? r->message : ""); break;
    }
}
