#include "compiler.h"
#include "fine.h"
#include "proof.h"
#include "runtime.h"

/* ------------------------------------------------------------------ */
/* registries                                                            */

typedef struct {
    ContextId params; size_t n; DiagNode *nodes;
    RefId B, o;               /* output type and term (ordinary) */
    RefId Z;                  /* terminal type (residual) */
    uint64_t lB;              /* level of B (or of Z) */
    bool residual;
    /* computed once */
    TermVarId y;              /* y_d : B (ordinary) */
    RefId *R;                 /* R_k for k = 0..n (R_n = Path_B(o, y) or Z) */
    uint64_t *RL;             /* the universe level of R_k */
    MapId nu; RefId C;        /* canonical substitution and value */
    bool built;
    /* cached maps */
    RefId collapse, expand; TermVarId r_slot, q_slot;
    /* validation */
    int valid_state; FaceId valid_face; const char *valid_reason;   /* 0 none, 1 valid, 2 invalid */
    uint64_t valid_session, valid_env;                              /* the checker session and environment the verdict belongs to */
} Diagram;

typedef struct {
    EvidenceKind kind;
    IdentityDecl decl;                                /* IDENTITY */
    ContextId params; FaceId req; RefId X, Y, e, B, C, D, R, k;   /* the others */
    uint64_t lX, lY, lB;
    DiagramId L, Rd;
} Certificate;
typedef struct { TransformId transform; size_t cert; } ProvEntry;

static struct {
    VEC(Diagram *) diagrams;
    VEC(CompiledTransform *) transforms;
    VEC(GraphPairTemplate *) pairs;
    VEC(Certificate *) certs;
    VEC(ProvEntry) prov;          /* §77.1: (transform, certificate) source associations */
    WordMap tindex;           /* §59.3: structural compiled-record key → transform id */
    WordMap dindex;           /* structural diagram key → diagram id */
    pthread_mutex_t mu; pthread_cond_t cv;
    bool init;
} CR;

void compiler_init(void) {
    memset(&CR, 0, sizeof CR);
    pthread_mutex_init(&CR.mu, NULL); pthread_cond_init(&CR.cv, NULL);
    wordmap_init(&CR.tindex); wordmap_init(&CR.dindex);
    CR.init = true;
    rt_init(); proof_init();   /* §R5: the runtime-construction and proof-use modules belong to the same serial lifecycle */
}
void compiler_free(void) {
    proof_free(); rt_free();          /* the proof-use boundary caches reference compiler records */
    if (!CR.init) return;
    for (size_t k = 0; k < CR.diagrams.len; k++) { free(CR.diagrams.data[k]->nodes); free(CR.diagrams.data[k]->R); free(CR.diagrams.data[k]->RL); free(CR.diagrams.data[k]); }
    for (size_t k = 0; k < CR.transforms.len; k++) free(CR.transforms.data[k]);
    for (size_t k = 0; k < CR.pairs.len; k++) free(CR.pairs.data[k]);
    for (size_t k = 0; k < CR.certs.len; k++) free(CR.certs.data[k]);
    vec_free(&CR.diagrams); vec_free(&CR.transforms); vec_free(&CR.pairs); vec_free(&CR.certs); vec_free(&CR.prov);
    wordmap_free(&CR.tindex); wordmap_free(&CR.dindex);
    pthread_mutex_destroy(&CR.mu); pthread_cond_destroy(&CR.cv);
    memset(&CR, 0, sizeof CR);
}
static void ensure_init(void) { if (!CR.init) compiler_init(); }

/* the registry vector grows under CR.mu; a lookup takes the lock for the id
 * check and the stable heap pointer (the Diagram itself is retained until
 * compiler teardown). Callers never hold CR.mu while calling DG. */
static Diagram *DG(DiagramId d) {
    pthread_mutex_lock(&CR.mu);
    require(d >= 1 && d <= CR.diagrams.len, "unknown diagram");
    Diagram *p = CR.diagrams.data[d - 1];
    pthread_mutex_unlock(&CR.mu);
    return p;
}

/* ------------------------------------------------------------------ */
/* anchored names (§40): owning identity, compilation role, node, slot    */

enum { ROLE_Y = 1, ROLE_COLLAPSE_R, ROLE_EXPAND_Q, ROLE_DOWN_I, ROLE_DOWN_J,
       ROLE_PAIR_Y, ROLE_PAIR_P, ROLE_PAIR_RL, ROLE_PAIR_RR,
       ROLE_EQ_A, ROLE_EQ_B, ROLE_CUT_W, ROLE_CUT_H, ROLE_CUT_Z, ROLE_CUT_U, ROLE_CF_W, ROLE_CF_B, ROLE_CF_BIND,
       ROLE_RES_R, ROLE_RES_Q };

#define cterm_PARAMS(X) X(uint64_t, role) X(uint64_t, a) X(uint64_t, b) X(uint64_t, slot) X(RefId, type)
KF_DECL(cterm, TermVarId, cterm_PARAMS, KeyWord k[5]; TermVarId x;)
KF_STEP(cterm) {
    KF_BEGIN(cterm);
    F->k[0] = (KeyWord){ KW_CONST, 8000 }; F->k[1] = (KeyWord){ KW_CONST, F->role }; F->k[2] = (KeyWord){ KW_CONST, F->a }; F->k[3] = (KeyWord){ KW_CONST, F->b }; F->k[4] = (KeyWord){ KW_CONST, F->slot };
    KF_CALL(fresh_term_keyed, &F->x, F->k, 5, F->type);
    KF_RET(F->x);
    KF_END;
}
static TermVarId cterm(uint64_t role, uint64_t a, uint64_t b, uint64_t slot, RefId type) { TermVarId r; KStack *s_ = kf_sync_begin(); cterm_push(s_, &r, role, a, b, slot, type); kf_sync_run(s_); kf_sync_end(s_); return r; }
/* a formal whose declared type is itself keyed (the equivalence / cut
 * schemas are indexed by their type data) */
#define cterm_typed_PARAMS(X) X(uint64_t, role) X(uint64_t, a) X(RefId, type)
KF_DECL(cterm_typed, TermVarId, cterm_typed_PARAMS, KeyWord k[4]; TermVarId x;)
KF_STEP(cterm_typed) {
    KF_BEGIN(cterm_typed);
    F->k[0] = (KeyWord){ KW_CONST, 8001 }; F->k[1] = (KeyWord){ KW_CONST, F->role }; F->k[2] = (KeyWord){ KW_CONST, F->a }; F->k[3] = (KeyWord){ KW_REF, F->type };
    KF_CALL(fresh_term_keyed, &F->x, F->k, 4, F->type);
    KF_RET(F->x);
    KF_END;
}
static TermVarId cterm_typed(uint64_t role, uint64_t a, RefId type) { TermVarId r; KStack *s_ = kf_sync_begin(); cterm_typed_push(s_, &r, role, a, type); kf_sync_run(s_); kf_sync_end(s_); return r; }
static __attribute__((unused)) DimVarId cdim(uint64_t role, uint64_t a, uint64_t b, uint64_t slot) {
    KeyWord k[5] = { { KW_CONST, 8002 }, { KW_CONST, role }, { KW_CONST, a }, { KW_CONST, b }, { KW_CONST, slot } };
    return fresh_dim_keyed(k, 5);
}

/* ------------------------------------------------------------------ */
/* diagrams                                                              */

/* diagrams are interned by their structural declaration: the same
 * declaration (in the same environment) is one diagram */
static DiagramId diagram_new(ContextId params, size_t n, const DiagNode *nodes, RefId B, RefId o, RefId Z, uint64_t lB, bool residual) {
    ensure_init();
    Words w; words_init(&w);
    words_push(&w, global_env_version()); words_push(&w, params); words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, nodes[k].node_id); words_push(&w, nodes[k].x); words_push(&w, nodes[k].e); words_push(&w, nodes[k].A); words_push(&w, nodes[k].level); words_push(&w, nodes[k].t); }
    words_push(&w, B); words_push(&w, o); words_push(&w, Z); words_push(&w, lB); words_push(&w, residual);
    /* the declaration is interned outside CR.mu (the interner is internally
     * synchronized); the index under CR.mu is keyed by its one-word id */
    uint64_t kw[2] = { 0xD1A6, interner_intern(&M.keys, w.w, w.n, NULL) }; words_free(&w); words_init(&w); words_push(&w, kw[0]); words_push(&w, kw[1]);
    pthread_mutex_lock(&CR.mu);
    uint64_t have;
    if (wordmap_get(&CR.dindex, w.w, w.n, &have)) { pthread_mutex_unlock(&CR.mu); words_free(&w); return (DiagramId)have; }
    Diagram *d = calloc(1, sizeof *d); require(d, "out of memory");
    d->params = params; d->n = n;
    d->nodes = calloc(n ? n : 1, sizeof(DiagNode)); require(d->nodes, "out of memory");
    if (n) memcpy(d->nodes, nodes, n * sizeof(DiagNode));
    d->B = B; d->o = o; d->Z = Z; d->lB = lB; d->residual = residual;
    vec_push(&CR.diagrams, d);
    DiagramId id = CR.diagrams.len;
    wordmap_put(&CR.dindex, w.w, w.n, id);
    pthread_mutex_unlock(&CR.mu);
    words_free(&w);
    return id;
}
DiagramId diagram_declare(ContextId params, size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o) { return diagram_new(params, n, nodes, B, o, 0, lB, false); }
DiagramId residual_declare(ContextId params, size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ) { return diagram_new(params, n, nodes, 0, 0, Z, lZ, true); }
size_t diagram_nodes(DiagramId d, const DiagNode **nodes) { Diagram *g = DG(d); require(g, "unknown diagram"); *nodes = g->nodes; return g->n; }
RefId diagram_output(DiagramId d, RefId *B, uint64_t *lB, bool *residual) { Diagram *g = DG(d); require(g, "unknown diagram"); *B = g->B; *lB = g->lB; *residual = g->residual; return g->residual ? g->Z : g->o; }
ContextId diagram_params(DiagramId d) { Diagram *g = DG(d); require(g, "unknown diagram"); return g->params; }

/* the realization telescope, canonical substitution and value (§39) */
#define diagram_build_PARAMS(X) X(DiagramId, id)
KF_DECL_DROP(diagram_build, void, diagram_build_PARAMS, diagram_build_drop,
    Diagram *d; size_t n, k, q, nt; RefId *R; uint64_t *RL; TermVarId y; RefId Pk, t0, ak, Ak, C, vr, s2; uint64_t inner; MapBuilder b, c; MapId nu; bool built;)
static void diagram_build_drop(diagram_build_F *F) { free(F->R); free(F->RL); F->R = NULL; F->RL = NULL; words_free(&F->b.t); words_free(&F->b.d); words_free(&F->c.t); words_free(&F->c.d); }
KF_STEP(diagram_build) {
    KF_BEGIN(diagram_build);
    F->d = DG(F->id);
    pthread_mutex_lock(&CR.mu);
    F->built = F->d->built;
    pthread_mutex_unlock(&CR.mu);
    if (F->built) KF_RETV();
    F->n = F->d->n;
    F->R = calloc(F->n + 1, sizeof(RefId)); require(F->R, "out of memory");
    F->RL = calloc(F->n + 1, sizeof(uint64_t)); require(F->RL, "out of memory");
    F->y = 0;
    if (F->d->residual) { F->R[F->n] = F->d->Z; F->RL[F->n] = F->d->lB; }
    else { KF_CALL(cterm, &F->y, ROLE_Y, F->id, 0, 0, F->d->B); KF_CALL(ref_var, &F->vr, F->y); KF_CALL(mk_path_const, &F->R[F->n], F->d->lB, F->d->B, F->d->o, F->vr); F->RL[F->n] = F->d->lB; }
    for (F->k = F->n; F->k-- > 0; ) {
        KF_CALL(ref_var, &F->vr, F->d->nodes[F->k].x);
        KF_CALL(mk_path_const, &F->Pk, F->d->nodes[F->k].level, F->d->nodes[F->k].A, F->d->nodes[F->k].t, F->vr);
        KF_CALL(level_max, &F->inner, F->d->nodes[F->k].level, F->RL[F->k + 1]);
        KF_CALL(mk_sigma_lv, &F->s2, F->d->nodes[F->k].level, F->RL[F->k + 1], F->d->nodes[F->k].e, F->Pk, F->R[F->k + 1]);
        KF_CALL(mk_sigma_lv, &F->R[F->k], F->d->nodes[F->k].level, F->inner, F->d->nodes[F->k].x, F->d->nodes[F->k].A, F->s2);
        KF_CALL(level_max, &F->RL[F->k], F->d->nodes[F->k].level, F->inner);
    }
    mapb_init(&F->b);
    KF_CALL(mapb_finish, &F->nu, &F->b);
    for (F->k = 0; F->k < F->n; F->k++) {
        KF_CALL(reindex, &F->ak, F->d->nodes[F->k].t, F->nu);
        KF_CALL(reindex, &F->Ak, F->d->nodes[F->k].A, F->nu);
        mapb_init(&F->c);
        F->nt = map_n_terms(F->nu);
        KF_MAPB_RESERVE(&F->c, F->nt + 2, 0);
        for (F->q = 0; F->q < F->nt; F->q++) { TermVarId x; RefId im; map_term_entry(F->nu, F->q, &x, &im); mapb_term(&F->c, x, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
        mapb_term(&F->c, F->d->nodes[F->k].x, F->ak);
        KF_CALL(mk_refl, &F->t0, F->d->nodes[F->k].level, F->Ak, F->ak);
        mapb_term(&F->c, F->d->nodes[F->k].e, F->t0);
        KF_CALL(mapb_finish, &F->nu, &F->c);
    }
    KF_CALL(reindex, &F->C, F->d->residual ? F->d->Z : F->d->o, F->nu);
    pthread_mutex_lock(&CR.mu);
    if (!F->d->built) { F->d->y = F->y; F->d->R = F->R; F->d->RL = F->RL; F->d->nu = F->nu; F->d->C = F->C; F->d->built = true; F->R = NULL; F->RL = NULL; }
    pthread_mutex_unlock(&CR.mu);
    free(F->R); free(F->RL); F->R = NULL; F->RL = NULL;
    KF_RETV();
    KF_END;
}
static void diagram_build(DiagramId id) { KStack *s_ = kf_sync_begin(); diagram_build_push(s_, NULL, id); kf_sync_run(s_); kf_sync_end(s_); }

TermVarId diagram_output_param(DiagramId d) { diagram_build(d); return DG(d)->y; }
RefId diagram_realization(DiagramId d) { diagram_build(d); return DG(d)->R[0]; }
MapId diagram_canonical_subst(DiagramId d) { diagram_build(d); return DG(d)->nu; }
KF_DECL_EXT(diagram_canonical, RefId, diagram_canonical_PARAMS, )
KF_STEP(diagram_canonical) { KF_BEGIN(diagram_canonical); KF_CALL(diagram_build, NULL, F->d); KF_RET(DG(F->d)->C); KF_END; }
KF_SYNC_DEF(diagram_canonical, RefId, diagram_canonical_PARAMS, diagram_canonical(DiagramId d))

CheckStatus diagram_validate(DiagramId id, FaceId required, const char **reason) {
    Diagram *d = DG(id);
    /* a cached verdict belongs to one checker session and one environment:
     * after a session reset its diagnostic text is dead and its semantic
     * outcome is not the new environment's; revalidate */
    pthread_mutex_lock(&CR.mu);
    int vs = d->valid_state; FaceId vf = d->valid_face; const char *vr = d->valid_reason;
    bool current = d->valid_session == check_session_id() && d->valid_env == global_env_version();
    pthread_mutex_unlock(&CR.mu);
    if (vs && current && vf == required) { if (vs == 2) *reason = vr; return vs == 1 ? CK_VALID : CK_INVALID; }
    CheckStatus st = check_context(d->params, reason);
    ContextId G = d->params;
    for (size_t k = 0; k < d->n && st == CK_VALID; k++) {
        const DiagNode *nd = &d->nodes[k];
        /* A_k is a type and t_k : A_k in Γ, x_0, e_0, …, x_{k-1}, e_{k-1} under the face */
        uint64_t lv;
        st = check_is_type(G, required, nd->A, &lv, reason);
        if (st != CK_VALID) { if (st == CK_INVALID) *reason = "node type is not a type"; break; }
        if (lv != nd->level) { *reason = "node type level annotation differs from its formation level"; st = CK_INVALID; break; }
        st = check(G, required, nd->t, nd->A, reason);
        if (st != CK_VALID) break;
        if (term_var_type(nd->x) != nd->A) { *reason = "node value variable is not declared at the node type"; st = CK_INVALID; break; }
        RefId Pk = mk_path_const(nd->level, nd->A, nd->t, ref_var(nd->x));
        if (term_var_type(nd->e) != Pk) { *reason = "node witness variable is not declared at Path_A(t, x)"; st = CK_INVALID; break; }
        G = context_extend_term(context_extend_term(G, nd->x, nd->A), nd->e, Pk);
        st = check_context(G, reason);
    }
    if (st == CK_VALID) {
        uint64_t lv;
        if (d->residual) { st = check_is_type(G, required, d->Z, &lv, reason); if (st == CK_INVALID) *reason = "residual terminal is not a type"; }
        else {
            st = check_is_type(d->params, required, d->B, &lv, reason);        /* B is in Γ */
            if (st == CK_INVALID) *reason = "output type is not a type";
            else if (st == CK_VALID) st = check(G, required, d->o, d->B, reason);
        }
        if (st == CK_VALID && lv != d->lB) { *reason = "output/terminal type level annotation differs from its formation level"; st = CK_INVALID; }
    }
    if (st == CK_VALID) {
        /* the realization type must itself be a type in a universe */
        diagram_build(id);
        uint64_t lv;
        ContextId Gy = d->residual ? d->params : context_extend_term(d->params, d->y, d->B);
        st = check_is_type(Gy, required, d->R[0], &lv, reason);
        if (st == CK_INVALID) *reason = "realization type is not a type";
    }
    if (st != CK_UNRESOLVED) {
        pthread_mutex_lock(&CR.mu);
        d->valid_state = st == CK_VALID ? 1 : 2; d->valid_face = required; d->valid_reason = *reason;
        d->valid_session = check_session_id(); d->valid_env = global_env_version();
        pthread_mutex_unlock(&CR.mu);
    }
    return st;
}

/* ------------------------------------------------------------------ */
/* singleton contraction and expansion (§41)                             */

/* Down(A, t, D, x, e, z) with D the scope [x_k:A, e_k:Path_A(t,x_k)] over the
 * tail R_{k+1}[prefix] (§54): the fixed template applies D by contextual
 * substitution; uses of e are ordinary path applications */
static RefId down(DiagramId id, size_t k, RefId A, uint64_t lA, RefId t, RefId D, uint64_t lD, TermVarId xk, TermVarId ek, RefId x, RefId e, RefId z) {
    (void)id;
    RefId Pk = mk_path_const(lA, A, t, ref_var(xk));
    ScopeId Ds = capture_term2(xk, A, lA, ek, Pk, lA, D, mk_universe(lD), level_succ(lD), fc_true());
    return mk_down(lD, lA, A, t, Ds, x, e, z);
}

static MapId extend2(MapId prefix, TermVarId x, RefId xi, TermVarId e, RefId ei) {
    MapBuilder b; mapb_init(&b);
    size_t nt = map_n_terms(prefix);
    for (size_t q = 0; q < nt; q++) { TermVarId v; RefId im; map_term_entry(prefix, q, &v, &im); mapb_term(&b, v, im); }
    mapb_term(&b, x, xi); mapb_term(&b, e, ei);
    return mapb_finish(&b);
}

static RefId emit_collapse(DiagramId id, size_t k, MapId prefix, RefId r) {
    Diagram *d = DG(id);
    if (k == d->n) return r;
    const DiagNode *nd = &d->nodes[k];
    RefId A = reindex(nd->A, prefix), t = reindex(nd->t, prefix), D = reindex(d->R[k + 1], prefix);
    RefId x = mk_fst(r), e = mk_fst(mk_snd(r)), z = mk_snd(mk_snd(r));
    RefId z0 = down(id, k, A, nd->level, t, D, d->RL[k + 1], nd->x, nd->e, x, e, z);
    MapId next = extend2(prefix, nd->x, t, nd->e, mk_refl(nd->level, A, t));
    return emit_collapse(id, k + 1, next, z0);
}

static RefId emit_expand(DiagramId id, size_t k, MapId prefix, RefId q) {
    Diagram *d = DG(id);
    if (k == d->n) return q;
    const DiagNode *nd = &d->nodes[k];
    RefId A = reindex(nd->A, prefix), t = reindex(nd->t, prefix);
    MapId next = extend2(prefix, nd->x, t, nd->e, mk_refl(nd->level, A, t));
    RefId z0 = emit_expand(id, k + 1, next, q);
    RefId S = reindex(d->R[k], prefix);                 /* Σ(x_k:A).Σ(e_k:Path(t,x_k)).R_{k+1} */
    RefId inner = apply_term_binder(S, 0, 1, t);        /* Σ(e_k:Path(t,t)).R_{k+1}[x_k ↦ t] */
    uint64_t linner = level_max(nd->level, d->RL[k + 1]);
    return mk_pair_at_lv(d->RL[k], S, t, mk_pair_at_lv(linner, inner, mk_refl(nd->level, A, t), z0));
}

RefId diagram_collapse(DiagramId id, TermVarId *r_slot) {
    diagram_build(id);
    Diagram *d = DG(id);
    pthread_mutex_lock(&CR.mu); RefId c = d->collapse; TermVarId r = d->r_slot; pthread_mutex_unlock(&CR.mu);
    if (!c) {
        r = cterm(ROLE_COLLAPSE_R, id, 0, 0, d->R[0]);
        c = emit_collapse(id, 0, map_identity(), ref_var(r));
        pthread_mutex_lock(&CR.mu); if (!d->collapse) { d->collapse = c; d->r_slot = r; } pthread_mutex_unlock(&CR.mu);
    }
    if (r_slot) *r_slot = r;
    return c;
}
RefId diagram_expand(DiagramId id, TermVarId *q_slot) {
    diagram_build(id);
    Diagram *d = DG(id);
    pthread_mutex_lock(&CR.mu); RefId x = d->expand; TermVarId q = d->q_slot; pthread_mutex_unlock(&CR.mu);
    if (!x) {
        RefId Qt = reindex(d->R[d->n], d->nu);           /* Path_B(C, y) (residual: Z[ν]) */
        q = cterm(ROLE_EXPAND_Q, id, 0, 0, Qt);
        x = emit_expand(id, 0, map_identity(), ref_var(q));
        pthread_mutex_lock(&CR.mu); if (!d->expand) { d->expand = x; d->q_slot = q; } pthread_mutex_unlock(&CR.mu);
    }
    if (q_slot) *q_slot = q;
    return x;
}

/* ------------------------------------------------------------------ */
/* publication                                                           */

/* the structural compiled-record key (§59.3): the environment, the schema,
 * every certificate input and the derived record data; no registry numbers */
/* §77.1: the action key is semantic content only — the schema, its typed
 * inputs and the derived record; neither the source declaration's id nor the
 * environment counter nor any registry number. Source declarations are kept
 * in a separate provenance index (transform_sources). */
static void record_key(const Certificate *c, const CompiledTransform *t, Words *w) {
    words_init(w);
    words_push(w, c->kind);
    words_push(w, c->decl.parameters); words_push(w, c->decl.required_face); words_push(w, c->decl.result_type); words_push(w, c->decl.result_level);
    words_push(w, c->decl.left); words_push(w, c->decl.right); words_push(w, c->decl.evidence);
    words_push(w, c->params); words_push(w, c->req); words_push(w, c->X); words_push(w, c->Y); words_push(w, c->e); words_push(w, c->B); words_push(w, c->C); words_push(w, c->D); words_push(w, c->R); words_push(w, c->k);
    words_push(w, c->lX); words_push(w, c->lY); words_push(w, c->lB); words_push(w, c->L); words_push(w, c->Rd);
    words_push(w, t->parameters); words_push(w, t->required_face); words_push(w, t->domain); words_push(w, t->codomain); words_push(w, t->domain_level); words_push(w, t->codomain_level);
    words_push(w, t->forward_argument_slot); words_push(w, t->reverse_argument_slot); words_push(w, t->forward_body); words_push(w, t->reverse_body); words_push(w, t->evidence_kind);
}
/* §59.3: the fixed call origin of one orientation over the parameters and
 * the argument slot; invocations are views of it */
static RefId build_generic_call(TransformId id, int dir, const CompiledTransform *t) {
    size_t n = context_size(t->parameters);
    Field *f = malloc((n ? n : 1) * sizeof(Field)); require(f, "out of memory");
    for (size_t k = 0; k < n; k++) {
        CtxDecl d = context_decl(t->parameters, k);
        if (d.sort == S_TERM) f[k] = (Field){ F_REF, NO_SLOT, ref_var(d.id) };
        else f[k] = (Field){ F_INTERVAL, NO_SLOT, iv_var(d.id) };
    }
    TermVarId slot = dir ? t->reverse_argument_slot : t->forward_argument_slot;
    RefId in = dir ? t->codomain : t->domain, out = dir ? t->domain : t->codomain;
    RefId r = mk_tcall(id, dir, n, f, ref_var(slot), in, out, t->required_face);
    free(f);
    return r;
}
/* a compiled record becomes visible only after both call bodies exist; the
 * whole-environment admission gate (§57 R1) guards publication */
/* a compiled record becomes visible only after both call bodies exist; the
 * whole-environment admission gate (§57 R1) guards publication; structurally
 * identical requests (sequential or concurrent) obtain one record */
static TransformId transform_publish(CompiledTransform *t, Certificate *c, const char **reason) {
    if (check_admission(reason) != CK_VALID) return 0;
    Words key; record_key(c, t, &key);
    { uint64_t kid = interner_intern(&M.keys, key.w, key.n, NULL); key.n = 0; words_push(&key, 0x7EC0); words_push(&key, kid); }   /* interned outside CR.mu; a one-word index key under it */
    pthread_mutex_lock(&CR.mu);
    uint64_t have;
    if (wordmap_get(&CR.tindex, key.w, key.n, &have)) {
        /* the same action: record this source declaration as a further
         * provenance receipt and join its publication */
        if (c->kind == EV_IDENTITY) { Certificate *cp = malloc(sizeof *cp); require(cp, "out of memory"); *cp = *c; vec_push(&CR.certs, cp); { ProvEntry pe = { (TransformId)have, CR.certs.len }; vec_push(&CR.prov, pe); } }
        while (!CR.transforms.data[have - 1]->generic_call[1]) pthread_cond_wait(&CR.cv, &CR.mu);
        pthread_mutex_unlock(&CR.mu); words_free(&key);
        return (TransformId)have;
    }
    Certificate *cp = malloc(sizeof *cp); require(cp, "out of memory"); *cp = *c;
    vec_push(&CR.certs, cp);
    CompiledTransform *p = malloc(sizeof *p); require(p, "out of memory"); *p = *t;
    p->certificate = CR.certs.len;
    { ProvEntry pe = { (TransformId)(CR.transforms.len + 1), CR.certs.len }; vec_push(&CR.prov, pe); }
    p->generic_call[0] = p->generic_call[1] = 0;
    vec_push(&CR.transforms, p); p->id = CR.transforms.len;       /* id reserved and key claimed; not yet visible */
    wordmap_put(&CR.tindex, key.w, key.n, p->id);
    pthread_mutex_unlock(&CR.mu);
    words_free(&key);
    RefId g0 = build_generic_call(p->id, DIR_FORWARD, p), g1 = build_generic_call(p->id, DIR_REVERSE, p);
    pthread_mutex_lock(&CR.mu); p->generic_call[0] = g0; p->generic_call[1] = g1; pthread_cond_broadcast(&CR.cv); pthread_mutex_unlock(&CR.mu);
    return p->id;
}
const CompiledTransform *transform_get(TransformId id) {
    if (!CR.init) return NULL;
    pthread_mutex_lock(&CR.mu);
    const CompiledTransform *t = (id >= 1 && id <= CR.transforms.len) ? CR.transforms.data[id - 1] : NULL;
    if (t && !t->generic_call[1]) t = NULL;                 /* reserved, not yet published */
    pthread_mutex_unlock(&CR.mu);
    return t;
}
const GraphPairTemplate *graph_pair_get(uint64_t id) {
    pthread_mutex_lock(&CR.mu); const GraphPairTemplate *t = (id >= 1 && id <= CR.pairs.len) ? CR.pairs.data[id - 1] : NULL; pthread_mutex_unlock(&CR.mu);
    return t;
}
size_t transform_count(void) { if (!CR.init) return 0; pthread_mutex_lock(&CR.mu); size_t n = CR.transforms.len; pthread_mutex_unlock(&CR.mu); return n; }

/* ------------------------------------------------------------------ */
/* identity compilation (§42)                                            */

static MapId map2(TermVarId x, RefId a, TermVarId y, RefId b) { MapBuilder m; mapb_init(&m); mapb_term(&m, x, a); mapb_term(&m, y, b); return mapb_finish(&m); }

/* the generic proof-parameterized template of the ordered pair (L, R),
 * cached by the pair */
static const GraphPairTemplate *graph_pair(DiagramId L, DiagramId R, RefId B, uint64_t lB, ContextId params) {
    pthread_mutex_lock(&CR.mu);
    for (size_t k = 0; k < CR.pairs.len; k++) if (CR.pairs.data[k]->left == L && CR.pairs.data[k]->right == R) { const GraphPairTemplate *t = CR.pairs.data[k]; pthread_mutex_unlock(&CR.mu); return t; }
    pthread_mutex_unlock(&CR.mu);
    GraphPairTemplate t; memset(&t, 0, sizeof t);
    t.left = L; t.right = R;
    t.y = cterm(ROLE_PAIR_Y, L, R, 0, B);
    RefId y = ref_var(t.y);
    RefId CL = diagram_canonical(L), CRr = diagram_canonical(R);
    TermVarId yL = diagram_output_param(L), yR = diagram_output_param(R);
    t.domain = reindex1(diagram_realization(L), yL, y);
    t.codomain = reindex1(diagram_realization(R), yR, y);
    t.P = cterm(ROLE_PAIR_P, L, R, 0, mk_path_const(lB, B, CL, CRr));
    t.r_left = cterm(ROLE_PAIR_RL, L, R, 0, t.domain);
    t.r_right = cterm(ROLE_PAIR_RR, L, R, 0, t.codomain);
    RefId P = ref_var(t.P);
    TermVarId rL, rR, qL, qR;
    RefId cL = diagram_collapse(L, &rL), cR = diagram_collapse(R, &rR);
    RefId dL = diagram_expand(L, &qL), dR = diagram_expand(R, &qR);
    /* forward = d_R(concat(inverse(P), c_L(r_L))) */
    RefId cLr = reindex(cL, map2(rL, ref_var(t.r_left), yL, y));           /* : Path_B(C_L, y) */
    RefId invP = mk_path_rev(lB, B, CL, CRr, P);                            /* : Path_B(C_R, C_L) */
    RefId qf = mk_path_concat(lB, B, CRr, CL, y, invP, cLr);                /* : Path_B(C_R, y) */
    t.forward = reindex(dR, map2(qR, qf, yR, y));
    /* reverse = d_L(concat(P, c_R(r_R))) */
    RefId cRr = reindex(cR, map2(rR, ref_var(t.r_right), yR, y));          /* : Path_B(C_R, y) */
    RefId qb = mk_path_concat(lB, B, CL, CRr, y, P, cRr);                   /* : Path_B(C_L, y) */
    t.reverse = reindex(dL, map2(qL, qb, yL, y));
    t.parameters = context_extend_term(params, t.y, B);
    GraphPairTemplate *p = malloc(sizeof *p); require(p, "out of memory"); *p = t;
    pthread_mutex_lock(&CR.mu);
    for (size_t k = 0; k < CR.pairs.len; k++) if (CR.pairs.data[k]->left == L && CR.pairs.data[k]->right == R) { const GraphPairTemplate *q = CR.pairs.data[k]; pthread_mutex_unlock(&CR.mu); free(p); return q; }
    vec_push(&CR.pairs, p); p->id = CR.pairs.len;
    pthread_mutex_unlock(&CR.mu);
    return p;
}

/* the derivation (validation + emission) shared by compilation and
 * certificate verification; fills *out without publishing */
static CheckStatus derive_identity(const IdentityDecl *d, CompiledTransform *out, const char **reason) {
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(d->parameters, reason);
    if (st != CK_VALID) return st;
    { size_t n = context_size(d->parameters); Words dims; words_init(&dims); fc_dims(d->required_face, &dims);
      for (size_t k = 0; k < dims.n; k++) if (!context_declares_dim(d->parameters, dims.w[k])) { words_free(&dims); *reason = "required face mentions an undeclared dimension"; return CK_INVALID; }
      words_free(&dims); (void)n; }
    { uint64_t lv; st = check_is_type(d->parameters, d->required_face, d->result_type, &lv, reason);
      if (st != CK_VALID) { if (st == CK_INVALID) *reason = "result type is not a type"; return st; }
      if (lv != d->result_level) { *reason = "result type level annotation differs from its formation level"; return CK_INVALID; } }
    if (DG(d->left)->params != d->parameters || DG(d->right)->params != d->parameters) { *reason = "diagram parameter context differs from the declaration's"; return CK_INVALID; }
    if (DG(d->left)->residual || DG(d->right)->residual) { *reason = "an identity declaration takes ordinary diagrams"; return CK_INVALID; }
    if (DG(d->left)->B != d->result_type || DG(d->right)->B != d->result_type || DG(d->left)->lB != d->result_level || DG(d->right)->lB != d->result_level) { *reason = "diagram output type differs from the result type"; return CK_INVALID; }
    st = diagram_validate(d->left, d->required_face, reason); if (st != CK_VALID) return st;
    st = diagram_validate(d->right, d->required_face, reason); if (st != CK_VALID) return st;
    RefId CL = diagram_canonical(d->left), CRr = diagram_canonical(d->right);
    st = check(d->parameters, d->required_face, d->evidence, mk_path_const(d->result_level, d->result_type, CL, CRr), reason);
    if (st != CK_VALID) { if (st == CK_INVALID) *reason = "evidence is not a path between the canonical values"; return st; }
    const GraphPairTemplate *t = graph_pair(d->left, d->right, d->result_type, d->result_level, d->parameters);
    out->parameters = t->parameters;
    out->required_face = d->required_face;
    out->domain = t->domain; out->codomain = t->codomain;
    out->domain_level = DG(d->left)->RL[0]; out->codomain_level = DG(d->right)->RL[0];
    out->forward_argument_slot = t->r_left; out->reverse_argument_slot = t->r_right;
    out->forward_body = reindex1(t->forward, t->P, d->evidence);
    out->reverse_body = reindex1(t->reverse, t->P, d->evidence);
    out->evidence_kind = EV_IDENTITY;
    out->identity_template = t->id;
    ContextId GL = context_extend_term(t->parameters, t->r_left, t->domain), GR = context_extend_term(t->parameters, t->r_right, t->codomain);
    st = check_context(GL, reason); if (st != CK_VALID) return st;
    st = check_context(GR, reason); if (st != CK_VALID) return st;
    st = check(GL, d->required_face, out->forward_body, out->codomain, reason);
    if (st != CK_VALID) { if (st == CK_INVALID) *reason = "generated forward body does not check"; return st; }
    st = check(GR, d->required_face, out->reverse_body, out->domain, reason);
    if (st != CK_VALID) { if (st == CK_INVALID) *reason = "generated reverse body does not check"; return st; }
    return CK_VALID;
}

TransformId compile_identity(const IdentityDecl *d, const char **reason) {
    ensure_init();
    CompiledTransform t;
    if (derive_identity(d, &t, reason) != CK_VALID) return 0;
    Certificate c; memset(&c, 0, sizeof c); c.kind = EV_IDENTITY; c.decl = *d;
    return transform_publish(&t, &c, reason);
}

/* ------------------------------------------------------------------ */
/* equivalences, residuals, cuts, contractible fibres (§44)              */

static CheckStatus derive_equivalence(ContextId params, FaceId req, RefId X, uint64_t lX, RefId Y, uint64_t lY, RefId e, CompiledTransform *out, const char **reason) {
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    uint64_t lv;
    st = check_is_type(params, req, X, &lv, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "X is not a type"; return st; }
    if (lv != lX) { *reason = "X level annotation differs"; return CK_INVALID; }
    st = check_is_type(params, req, Y, &lv, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "Y is not a type"; return st; }
    if (lv != lY) { *reason = "Y level annotation differs"; return CK_INVALID; }
    st = check(params, req, e, mk_equiv(lX, lY, X, Y), reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "e is not an equivalence X ≃ Y"; return st; }
    out->domain_level = lX; out->codomain_level = lY;
    /* forward(a) = (fst e)(a); reverse(b) = fst(fst((snd e)(b))) */
    TermVarId a = cterm_typed(ROLE_EQ_A, e, X), b = cterm_typed(ROLE_EQ_B, e, Y);
    out->parameters = params; out->required_face = req;
    out->domain = X; out->codomain = Y;
    out->forward_argument_slot = a; out->reverse_argument_slot = b;
    out->forward_body = mk_app(equiv_map(lX, lY, X, Y, e), ref_var(a));
    out->reverse_body = mk_fst(mk_fst(equiv_contr(lX, lY, X, Y, e, ref_var(b))));
    out->evidence_kind = EV_EQUIVALENCE;
    { ContextId Ga = context_extend_term(params, a, X), Gb2 = context_extend_term(params, b, Y);
      st = check_context(Ga, reason); if (st != CK_VALID) return st;
      st = check_context(Gb2, reason); if (st != CK_VALID) return st;
      st = check(Ga, req, out->forward_body, Y, reason); if (st != CK_VALID) return st;
      st = check(Gb2, req, out->reverse_body, X, reason); if (st != CK_VALID) return st; }
    return CK_VALID;
}
TransformId compile_equivalence(ContextId params, FaceId req, RefId X, uint64_t lX, RefId Y, uint64_t lY, RefId e, const char **reason) {
    ensure_init();
    CompiledTransform t;
    if (derive_equivalence(params, req, X, lX, Y, lY, e, &t, reason) != CK_VALID) return 0;
    Certificate c; memset(&c, 0, sizeof c); c.kind = EV_EQUIVALENCE; c.params = params; c.req = req; c.X = X; c.Y = Y; c.lX = lX; c.lY = lY; c.e = e;
    return transform_publish(&t, &c, reason);
}

static CheckStatus derive_residual(ContextId params, FaceId req, DiagramId L, DiagramId R, RefId e, CompiledTransform *out, const char **reason) {
    memset(out, 0, sizeof *out);
    if (!DG(L)->residual || !DG(R)->residual) { *reason = "a residual equivalence takes residual descriptions"; return CK_INVALID; }
    if (DG(L)->params != params || DG(R)->params != params) { *reason = "description parameter context differs"; return CK_INVALID; }
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    st = diagram_validate(L, req, reason); if (st != CK_VALID) return st;
    st = diagram_validate(R, req, reason); if (st != CK_VALID) return st;
    RefId ZL = diagram_canonical(L), ZR = diagram_canonical(R);     /* canonically instantiated terminal types */
    st = check(params, req, e, mk_equiv(DG(L)->lB, DG(R)->lB, ZL, ZR), reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "e is not an equivalence between the terminal types"; return st; }
    out->domain_level = DG(L)->RL[0]; out->codomain_level = DG(R)->RL[0];
    TermVarId rL, rR, qL, qR;
    RefId cL = diagram_collapse(L, &rL), cR = diagram_collapse(R, &rR);
    RefId dL = diagram_expand(L, &qL), dR = diagram_expand(R, &qR);
    out->parameters = params; out->required_face = req;
    out->domain = diagram_realization(L); out->codomain = diagram_realization(R);
    TermVarId r = cterm(ROLE_RES_R, L, R, 0, out->domain), q = cterm(ROLE_RES_Q, L, R, 0, out->codomain);
    out->forward_argument_slot = r; out->reverse_argument_slot = q;
    /* forward = d_R ∘ e.map ∘ c_L ; reverse = d_L ∘ e⁻¹ ∘ c_R with e⁻¹(b) = fst(fst((snd e) b)) */
    RefId zl = reindex1(cL, rL, ref_var(r));
    out->forward_body = reindex1(dR, qR, mk_app(equiv_map(DG(L)->lB, DG(R)->lB, ZL, ZR, e), zl));
    RefId zr = reindex1(cR, rR, ref_var(q));
    out->reverse_body = reindex1(dL, qL, mk_fst(mk_fst(equiv_contr(DG(L)->lB, DG(R)->lB, ZL, ZR, e, zr))));
    out->evidence_kind = EV_RESIDUAL_EQUIVALENCE;
    { ContextId Ga = context_extend_term(params, r, out->domain), Gb2 = context_extend_term(params, q, out->codomain);
      st = check_context(Ga, reason); if (st != CK_VALID) return st;
      st = check_context(Gb2, reason); if (st != CK_VALID) return st;
      st = check(Ga, req, out->forward_body, out->codomain, reason); if (st != CK_VALID) return st;
      st = check(Gb2, req, out->reverse_body, out->domain, reason); if (st != CK_VALID) return st; }
    return CK_VALID;
}
TransformId compile_residual_equivalence(ContextId params, FaceId req, DiagramId L, DiagramId R, RefId e, const char **reason) {
    ensure_init();
    CompiledTransform t;
    if (derive_residual(params, req, L, R, e, &t, reason) != CK_VALID) return 0;
    Certificate c; memset(&c, 0, sizeof c); c.kind = EV_RESIDUAL_EQUIVALENCE; c.params = params; c.req = req; c.L = L; c.Rd = R; c.e = e;
    return transform_publish(&t, &c, reason);
}

/* Cut(C,D) = Σ(z:B). Σ(u : C=z). (D=z) ; CUT_TO_PATH (z,u,v) ↦ u·v⁻¹ ; h ↦ (D, h, refl D) */
static RefId cut_type(uint64_t lB, RefId B, RefId C, RefId D, TermVarId *z_out, TermVarId *u_out) {
    TermVarId z = cterm_typed(ROLE_CUT_Z, C, B);
    RefId Cz = mk_path_const(lB, B, C, ref_var(z)), Dz = mk_path_const(lB, B, D, ref_var(z));
    TermVarId u = cterm_typed(ROLE_CUT_U, D, Cz);
    if (z_out) *z_out = z;
    if (u_out) *u_out = u;
    return mk_sigma_lv(lB, lB, z, B, mk_sigma_lv(lB, lB, u, Cz, Dz));
}
static CheckStatus derive_cut(ContextId params, FaceId req, RefId B, uint64_t lB, RefId C, RefId D, CompiledTransform *out, const char **reason) {
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    uint64_t lv;
    st = check_is_type(params, req, B, &lv, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "B is not a type"; return st; }
    if (lv != lB) { *reason = "B level annotation differs"; return CK_INVALID; }
    st = check(params, req, C, B, reason); if (st != CK_VALID) return st;
    st = check(params, req, D, B, reason); if (st != CK_VALID) return st;
    RefId Cut = cut_type(lB, B, C, D, NULL, NULL);
    RefId CD = mk_path_const(lB, B, C, D);
    out->domain_level = lB; out->codomain_level = lB;
    TermVarId w = cterm_typed(ROLE_CUT_W, D, Cut), h = cterm_typed(ROLE_CUT_H, C, CD);
    RefId z = mk_fst(ref_var(w)), u = mk_fst(mk_snd(ref_var(w))), v = mk_snd(mk_snd(ref_var(w)));
    out->parameters = params; out->required_face = req;
    out->domain = Cut; out->codomain = CD;
    out->forward_argument_slot = w; out->reverse_argument_slot = h;
    out->forward_body = mk_path_concat(lB, B, C, z, D, u, mk_path_rev(lB, B, D, z, v));
    RefId inner = apply_term_binder(Cut, 0, 1, D);        /* Σ(u : C=D). (D=D) */
    out->reverse_body = mk_pair_at_lv(lB, Cut, D, mk_pair_at_lv(lB, inner, ref_var(h), mk_refl(lB, B, D)));
    out->evidence_kind = EV_CUT;
    { ContextId Ga = context_extend_term(params, w, Cut), Gb2 = context_extend_term(params, h, CD);
      st = check_context(Ga, reason); if (st != CK_VALID) return st;
      st = check_context(Gb2, reason); if (st != CK_VALID) return st;
      st = check(Ga, req, out->forward_body, CD, reason); if (st != CK_VALID) return st;
      st = check(Gb2, req, out->reverse_body, Cut, reason); if (st != CK_VALID) return st; }
    return CK_VALID;
}
TransformId compile_cut(ContextId params, FaceId req, RefId B, uint64_t lB, RefId C, RefId D, const char **reason) {
    ensure_init();
    CompiledTransform t;
    if (derive_cut(params, req, B, lB, C, D, &t, reason) != CK_VALID) return 0;
    Certificate c; memset(&c, 0, sizeof c); c.kind = EV_CUT; c.params = params; c.req = req; c.B = B; c.lB = lB; c.C = C; c.D = D;
    return transform_publish(&t, &c, reason);
}

/* COLLAPSE_FIBRE: Σ(b:B).R(b) → B, (b,r) ↦ b ; reverse b ↦ (b, fst(k b)) with k : Π(b:B).Contr(R b) */
static CheckStatus derive_contractible(ContextId params, FaceId req, RefId B, uint64_t lB, RefId R, RefId k, CompiledTransform *out, const char **reason) {
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    uint64_t lv, lR;
    st = check_is_type(params, req, B, &lv, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "B is not a type"; return st; }
    if (lv != lB) { *reason = "B level annotation differs"; return CK_INVALID; }
    TermVarId bb = cterm_typed(ROLE_CF_BIND, R, B);
    /* R(b) must be a type for b : B */
    ContextId Gb = context_extend_term(params, bb, B);
    st = check_is_type(Gb, req, mk_app(R, ref_var(bb)), &lR, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "R(b) is not a type"; return st; }
    RefId Kt = mk_pi_lv(lB, lR, bb, B, mk_contr(lR, mk_app(R, ref_var(bb))));
    st = check(params, req, k, Kt, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "k is not a pointwise contraction of R"; return st; }
    RefId Sg = mk_sigma_lv(lB, lR, bb, B, mk_app(R, ref_var(bb)));
    out->domain_level = level_max(lB, lR); out->codomain_level = lB;
    TermVarId w = cterm_typed(ROLE_CF_W, k, Sg), b = cterm_typed(ROLE_CF_B, k, B);
    out->parameters = params; out->required_face = req;
    out->domain = Sg; out->codomain = B;
    out->forward_argument_slot = w; out->reverse_argument_slot = b;
    out->forward_body = mk_fst(ref_var(w));
    out->reverse_body = mk_pair_at_lv(level_max(lB, lR), Sg, ref_var(b), mk_fst(mk_app(k, ref_var(b))));
    out->evidence_kind = EV_CONTRACTIBLE_FIBRE;
    { ContextId Ga = context_extend_term(params, w, Sg), Gb2 = context_extend_term(params, b, B);
      st = check_context(Ga, reason); if (st != CK_VALID) return st;
      st = check_context(Gb2, reason); if (st != CK_VALID) return st;
      st = check(Ga, req, out->forward_body, B, reason); if (st != CK_VALID) return st;
      st = check(Gb2, req, out->reverse_body, Sg, reason); if (st != CK_VALID) return st; }
    return CK_VALID;
}
TransformId compile_contractible_fibre(ContextId params, FaceId req, RefId B, uint64_t lB, RefId R, RefId k, const char **reason) {
    ensure_init();
    CompiledTransform t;
    if (derive_contractible(params, req, B, lB, R, k, &t, reason) != CK_VALID) return 0;
    Certificate c; memset(&c, 0, sizeof c); c.kind = EV_CONTRACTIBLE_FIBRE; c.params = params; c.req = req; c.B = B; c.lB = lB; c.R = R; c.k = k;
    return transform_publish(&t, &c, reason);
}

/* ------------------------------------------------------------------ */
/* certificates (§39): re-emit and compare exactly                        */

CheckStatus certificate_verify(TransformId id, const char **reason) {
    const CompiledTransform *t = transform_get(id);
    if (!t) { *reason = "unknown transform"; return CK_INVALID; }
    pthread_mutex_lock(&CR.mu); Certificate c = *CR.certs.data[t->certificate - 1]; pthread_mutex_unlock(&CR.mu);
    CompiledTransform again; CheckStatus st;
    switch (c.kind) {
    case EV_IDENTITY: st = derive_identity(&c.decl, &again, reason); break;
    case EV_EQUIVALENCE: st = derive_equivalence(c.params, c.req, c.X, c.lX, c.Y, c.lY, c.e, &again, reason); break;
    case EV_RESIDUAL_EQUIVALENCE: st = derive_residual(c.params, c.req, c.L, c.Rd, c.e, &again, reason); break;
    case EV_CUT: st = derive_cut(c.params, c.req, c.B, c.lB, c.C, c.D, &again, reason); break;
    case EV_CONTRACTIBLE_FIBRE: st = derive_contractible(c.params, c.req, c.B, c.lB, c.R, c.k, &again, reason); break;
    default: *reason = "unknown certificate kind"; return CK_INVALID;
    }
    if (st != CK_VALID) return st;
    bool same = again.parameters == t->parameters && again.required_face == t->required_face &&
                again.domain == t->domain && again.codomain == t->codomain &&
                again.forward_argument_slot == t->forward_argument_slot && again.reverse_argument_slot == t->reverse_argument_slot &&
                again.forward_body == t->forward_body && again.reverse_body == t->reverse_body && again.evidence_kind == t->evidence_kind &&
                again.domain_level == t->domain_level && again.codomain_level == t->codomain_level;
    if (!same) { *reason = "registered record differs from the re-emitted derivation"; return CK_INVALID; }
    return CK_VALID;
}

KF_DECL_EXT(transform_evidence, bool, transform_evidence_PARAMS, const CompiledTransform *t; Certificate c; RefId cl, cr, x; TermVarId bb; ContextId Gb; uint64_t lR; RefId app, vb; CheckStatus ck; const char *why;)
KF_STEP(transform_evidence) {
    KF_BEGIN(transform_evidence);
    F->t = transform_get(F->id);
    if (!F->t) KF_RET(false);
    pthread_mutex_lock(&CR.mu); F->c = *CR.certs.data[F->t->certificate - 1]; pthread_mutex_unlock(&CR.mu);
    switch (F->c.kind) {
    case EV_IDENTITY:
        *F->G = F->c.decl.parameters; *F->face = F->c.decl.required_face; *F->evidence = F->c.decl.evidence;
        KF_CALL(diagram_canonical, &F->cl, F->c.decl.left); KF_CALL(diagram_canonical, &F->cr, F->c.decl.right);
        KF_CALL(mk_path_const, F->type, F->c.decl.result_level, F->c.decl.result_type, F->cl, F->cr);
        KF_RET(true);
    case EV_EQUIVALENCE:
        *F->G = F->c.params; *F->face = F->c.req; *F->evidence = F->c.e; KF_CALL(mk_equiv, F->type, F->c.lX, F->c.lY, F->c.X, F->c.Y); KF_RET(true);
    case EV_RESIDUAL_EQUIVALENCE:
        *F->G = F->c.params; *F->face = F->c.req; *F->evidence = F->c.e;
        KF_CALL(diagram_canonical, &F->cl, F->c.L); KF_CALL(diagram_canonical, &F->cr, F->c.Rd);
        KF_CALL(mk_equiv, F->type, DG(F->c.L)->lB, DG(F->c.Rd)->lB, F->cl, F->cr); KF_RET(true);
    case EV_CUT:
        KF_CALL(context_extend_term, F->G, F->t->parameters, F->t->forward_argument_slot, F->t->domain); *F->face = F->t->required_face; *F->evidence = F->t->forward_body; *F->type = F->t->codomain; KF_RET(true);
    case EV_CONTRACTIBLE_FIBRE: {
        KF_CALL(cterm_typed, &F->bb, ROLE_CF_BIND, F->c.R, F->c.B);
        KF_CALL(context_extend_term, &F->Gb, F->c.params, F->bb, F->c.B);
        KF_CALL(ref_var, &F->vb, F->bb);
        KF_CALL(mk_app, &F->app, F->c.R, F->vb);
        KF_CALL(check_is_type, &F->ck, F->Gb, F->c.req, F->app, &F->lR, &F->why);
        if (F->ck != CK_VALID) KF_RET(false);
        *F->G = F->c.params; *F->face = F->c.req; *F->evidence = F->c.k;
        KF_CALL(mk_contr, &F->x, F->lR, F->app);
        KF_CALL(mk_pi_lv, F->type, F->c.lB, F->lR, F->bb, F->c.B, F->x); KF_RET(true); }
    default: KF_RET(false);
    }
    KF_END;
}
KF_SYNC_DEF(transform_evidence, bool, transform_evidence_PARAMS, transform_evidence(TransformId id, ContextId *G, FaceId *face, RefId *evidence, RefId *type))

/* §77.1: the source declaration ids associated with an action (identity
 * declarations only; other schemas have no source id) */
size_t transform_sources(TransformId id, uint64_t *out, size_t cap) {
    size_t n = 0;
    pthread_mutex_lock(&CR.mu);
    for (size_t k = 0; k < CR.prov.len; k++) if (CR.prov.data[k].transform == id) { Certificate *c = CR.certs.data[CR.prov.data[k].cert - 1]; if (c->kind == EV_IDENTITY) { if (n < cap) out[n] = c->decl.id; n++; } }
    pthread_mutex_unlock(&CR.mu);
    return n;
}

/* ------------------------------------------------------------------ */
/* §80: the identity action as an ordinary open core term                 */

uint64_t identity_pair(DiagramId L, DiagramId R, RefId B, uint64_t lB, ContextId params) {
    ensure_init();
    require(DG(L) && DG(R), "unknown diagram");
    return graph_pair(L, R, B, lB, params)->id;
}
RefId identity_action(uint64_t pair, int dir, MapId sigma, RefId proof, RefId argument) {
    const GraphPairTemplate *t = graph_pair_get(pair);
    require(t, "unknown graph-pair template");
    /* one simultaneous map: σ on the diagram/common-output parameters,
     * P ↦ proof, r ↦ argument; the images are already in the target and are
     * not reindexed again; make_view restricts to the body's typed boundary */
    MapBuilder b; mapb_init(&b);
    size_t nt = map_n_terms(sigma), nd = map_n_dims(sigma);
    for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(sigma, k, &x, &im); if (x != t->P && x != t->r_left && x != t->r_right) mapb_term(&b, x, im); }
    for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(sigma, k, &i, &im); mapb_dim(&b, i, im); }
    mapb_term(&b, t->P, proof);
    mapb_term(&b, dir ? t->r_right : t->r_left, argument);
    return reindex(dir ? t->reverse : t->forward, mapb_finish(&b));
}

/* ------------------------------------------------------------------ */
/* invocation (§43)                                                      */

bool compiler_template(uint64_t id, int dir, RefId *body, TermVarId *slot) {
    const CompiledTransform *t = transform_get(id);
    if (!t) return false;
    *body = dir ? t->reverse_body : t->forward_body;
    *slot = dir ? t->reverse_argument_slot : t->forward_argument_slot;
    return true;
}

RefId mk_transform_call(TransformId id, int dir, MapId sigma, RefId a) {
    const CompiledTransform *t = transform_get(id);
    require(t, "TRANSFORM_CALL of an unknown transform");
    /* τ := σ restricted to the parameter context, extended by slot ↦ a (the
     * slot is fresh relative to the parameters: a is inserted once) */
    MapBuilder b; mapb_init(&b);
    size_t n = context_size(t->parameters);
    for (size_t k = 0; k < n; k++) {
        CtxDecl d = context_decl(t->parameters, k);
        if (d.sort == S_TERM) mapb_term(&b, d.id, map_term_image(sigma, d.id)); else mapb_dim(&b, d.id, map_dim_image(sigma, d.id));
    }
    mapb_term(&b, dir ? t->reverse_argument_slot : t->forward_argument_slot, a);
    return reindex(t->generic_call[dir ? 1 : 0], mapb_finish(&b));
}

KF_DECL_EXT_DROP(compiler_decode_call, bool, compiler_decode_call_PARAMS, compiler_decode_call_drop, const CompiledTransform *t; size_t n, k; MapBuilder b;)
static void compiler_decode_call_drop(compiler_decode_call_F *F) { words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(compiler_decode_call) {
    KF_BEGIN(compiler_decode_call);
    if (F->h->is_var || F->h->tag != T_TCALL) KF_RET(false);
    *F->id = F->h->payload / 2; *F->dir = (int)(F->h->payload & 1);
    F->t = transform_get(*F->id);
    if (!F->t) KF_RET(false);
    F->n = context_size(F->t->parameters);
    if (F->h->n != F->n + 3) KF_RET(false);
    mapb_init(&F->b);
    KF_MAPB_RESERVE(&F->b, F->n, F->n);
    for (F->k = 0; F->k < F->n; F->k++) {
        CtxDecl d = context_decl(F->t->parameters, F->k);
        if (d.sort == S_TERM) mapb_term(&F->b, d.id, F->h->f[F->k].id); else mapb_dim(&F->b, d.id, F->h->f[F->k].id);
        fine_bump(FC_MAP_ENTRIES); KF_SAFE();
    }
    KF_CALL(mapb_finish, F->sigma, &F->b);
    *F->a = F->h->f[F->n].id;
    KF_RET(true);
    KF_END;
}
KF_SYNC_DEF(compiler_decode_call, bool, compiler_decode_call_PARAMS, compiler_decode_call(const Head *h, uint64_t *id, int *dir, MapId *sigma, RefId *a))
