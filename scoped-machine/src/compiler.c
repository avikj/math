/* compiler.c — the input adapter (compiler.h). */
#include "compiler.h"
#include "eval.h"
#include "judge.h"

/* ------------------------------------------------------------------ */
/* the export memo: structural declaration key → diagram record          */

typedef struct {
    ContextId params; size_t n; DiagNode *nodes;
    RefId B, o;               /* output type and term (ordinary) */
    RefId Z;                  /* terminal type (residual) */
    uint64_t lB;              /* level of B (or of Z) */
    bool residual;
    /* the export (computed once, at declaration) */
    TermVarId y;              /* y : B (ordinary) */
    RefId *R; uint64_t *RL;   /* R_k for k = 0..n: the realization telescope (R_0 converts to R(y)) */
    MapId nu; RefId C;        /* canonical substitution and value */
    RefId value, vtype;       /* the Diagram / residual presentation and its type */
    RefId collapse, expand; TermVarId r_slot, q_slot;
} Diagram;

static struct {
    VEC(Diagram *) diagrams;
    WordMap dindex;
    pthread_mutex_t mu;
    bool init;
} CR;

void compiler_init(void) {
    memset(&CR, 0, sizeof CR);
    pthread_mutex_init(&CR.mu, NULL);
    wordmap_init(&CR.dindex);
    CR.init = true;
}
void compiler_free(void) {
    if (!CR.init) return;
    for (size_t k = 0; k < CR.diagrams.len; k++) { free(CR.diagrams.data[k]->nodes); free(CR.diagrams.data[k]->R); free(CR.diagrams.data[k]->RL); free(CR.diagrams.data[k]); }
    vec_free(&CR.diagrams); wordmap_free(&CR.dindex);
    pthread_mutex_destroy(&CR.mu);
    memset(&CR, 0, sizeof CR);
    rt_free();
}
static void ensure_init(void) { if (!CR.init) compiler_init(); }

/* a record is complete before its id is visible; it is immutable after */
static Diagram *DG(DiagramId d) {
    pthread_mutex_lock(&CR.mu);
    require(d >= 1 && d <= CR.diagrams.len, "unknown diagram");
    Diagram *p = CR.diagrams.data[d - 1];
    pthread_mutex_unlock(&CR.mu);
    return p;
}

/* formals keyed by content (§40): role and the data they range over */
enum { ROLE_Y = 1, ROLE_COLLAPSE_R, ROLE_EXPAND_Q, ROLE_CUT_Z, ROLE_CUT_U, ROLE_CF_BIND, ROLE_ACT_R };
static TermVarId keyed2(uint64_t role, uint64_t a, RefId type) {
    KeyWord k[4] = { { KW_CONST, 8001 }, { KW_CONST, role }, { KW_CONST, a }, { KW_REF, type } };
    return fresh_term_keyed(k, 4, type);
}

/* ------------------------------------------------------------------ */
/* the export of a declaration                                          */

/* the realization telescope, canonical substitution and value (§39) */
static void build_telescope(Diagram *d) {
    size_t n = d->n;
    d->R = calloc(n + 1, sizeof(RefId)); require(d->R, "out of memory");
    d->RL = calloc(n + 1, sizeof(uint64_t)); require(d->RL, "out of memory");
    if (d->residual) { d->R[n] = d->Z; d->RL[n] = d->lB; }
    else { d->y = keyed2(ROLE_Y, d->params, d->B); d->R[n] = mk_path_const(d->lB, d->B, d->o, ref_var(d->y)); d->RL[n] = d->lB; }
    for (size_t k = n; k-- > 0; ) {
        const DiagNode *nd = &d->nodes[k];
        RefId Pk = mk_path_const(nd->level, nd->A, nd->t, ref_var(nd->x));
        uint64_t inner = level_max(nd->level, d->RL[k + 1]);
        d->R[k] = mk_sigma_lv(nd->level, inner, nd->x, nd->A, mk_sigma_lv(nd->level, d->RL[k + 1], nd->e, Pk, d->R[k + 1]));
        d->RL[k] = level_max(nd->level, inner);
    }
    MapBuilder b; mapb_init(&b);
    MapId nu = mapb_finish(&b);
    for (size_t k = 0; k < n; k++) {
        const DiagNode *nd = &d->nodes[k];
        RefId ak = reindex(nd->t, nu), Ak = reindex(nd->A, nu);
        MapBuilder c; mapb_init(&c);
        size_t nt = map_n_terms(nu);
        for (size_t q = 0; q < nt; q++) { TermVarId x; RefId im; map_term_entry(nu, q, &x, &im); mapb_term(&c, x, im); }
        mapb_term(&c, nd->x, ak);
        mapb_term(&c, nd->e, mk_refl(nd->level, Ak, ak));
        nu = mapb_finish(&c);
    }
    d->nu = nu;
    d->C = reindex(d->residual ? d->Z : d->o, nu);
}

/* the value: the right fold of node ending in zero (§83.3), each node
 * instantiated by substitution at its tail λ x e. D_{k+1} */
static void build_value(Diagram *d) {
    size_t n = d->n;
    RefId D; uint64_t r = d->lB;
    if (d->residual) { RefId a[1] = { d->Z }; D = rt_inst(rt_recipe(RK_RES_ZERO, d->lB, 0, 0, 0), a); }
    else { RefId a[2] = { d->B, d->o }; D = rt_inst(rt_recipe(RK_ZERO, d->lB, 0, 0, 0), a); }
    for (size_t k = n; k-- > 0; ) {
        const DiagNode *nd = &d->nodes[k];
        RefId Pk = mk_path_const(nd->level, nd->A, nd->t, ref_var(nd->x));
        RefId Q = mk_lam_lv(nd->level, nd->x, nd->A, mk_lam_lv(nd->level, nd->e, Pk, D));
        if (d->residual) { RefId a[3] = { nd->A, nd->t, Q }; D = rt_inst(rt_recipe(RK_RES_NODE, nd->level, d->lB, r, 0), a); }
        else { RefId a[4] = { d->B, nd->A, nd->t, Q }; D = rt_inst(rt_recipe(RK_NODE, nd->level, d->lB, r, 0), a); }
        r = level_max(nd->level, r);
    }
    require(r == d->RL[0], "export level differs from the telescope level");
    d->value = D;
    d->vtype = d->residual ? rt_res_type(d->lB, r) : rt_diagram_type(d->lB, r, d->B);
    RefId M = d->residual ? rt_res_M(D) : rt_dg_M(D, ref_var(d->y));
    RefId Qt = d->residual ? d->C : mk_path_const(d->lB, d->B, d->C, ref_var(d->y));
    d->r_slot = keyed2(ROLE_COLLAPSE_R, 0, d->R[0]);
    d->q_slot = keyed2(ROLE_EXPAND_Q, 0, Qt);
    d->collapse = mk_app(rt_c(M), ref_var(d->r_slot));
    d->expand = mk_app(rt_d(M), ref_var(d->q_slot));
}

/* diagrams are memoized by their structural declaration */
static DiagramId diagram_new(ContextId params, size_t n, const DiagNode *nodes, RefId B, RefId o, RefId Z, uint64_t lB, bool residual) {
    ensure_init();
    Words w; words_init(&w);
    words_push(&w, params); words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, nodes[k].node_id); words_push(&w, nodes[k].x); words_push(&w, nodes[k].e); words_push(&w, nodes[k].A); words_push(&w, nodes[k].level); words_push(&w, nodes[k].t); }
    words_push(&w, B); words_push(&w, o); words_push(&w, Z); words_push(&w, lB); words_push(&w, residual);
    pthread_mutex_lock(&CR.mu);                 /* one export per key: built under the memo lock */
    uint64_t have;
    if (wordmap_get(&CR.dindex, w.w, w.n, &have)) { pthread_mutex_unlock(&CR.mu); words_free(&w); return (DiagramId)have; }
    Diagram *d = calloc(1, sizeof *d); require(d, "out of memory");
    d->params = params; d->n = n;
    d->nodes = calloc(n ? n : 1, sizeof(DiagNode)); require(d->nodes, "out of memory");
    if (n) memcpy(d->nodes, nodes, n * sizeof(DiagNode));
    d->B = B; d->o = o; d->Z = Z; d->lB = lB; d->residual = residual;
    build_telescope(d);
    build_value(d);
    vec_push(&CR.diagrams, d);
    DiagramId id = CR.diagrams.len;
    wordmap_put(&CR.dindex, w.w, w.n, id);
    pthread_mutex_unlock(&CR.mu);
    words_free(&w);
    return id;
}
DiagramId diagram_declare(ContextId params, size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o) { return diagram_new(params, n, nodes, B, o, 0, lB, false); }
DiagramId residual_declare(ContextId params, size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ) { return diagram_new(params, n, nodes, 0, 0, Z, lZ, true); }

TermVarId diagram_output_param(DiagramId d) { return DG(d)->y; }
RefId diagram_realization(DiagramId d) { return DG(d)->R[0]; }
RefId diagram_canonical(DiagramId d) { return DG(d)->C; }
RefId diagram_value(DiagramId d) { return DG(d)->value; }
RefId diagram_value_type(DiagramId d) { return DG(d)->vtype; }
uint64_t diagram_level(DiagramId d) { return DG(d)->RL[0]; }
RefId diagram_collapse(DiagramId d, TermVarId *r_slot) { Diagram *p = DG(d); if (r_slot) *r_slot = p->r_slot; return p->collapse; }
RefId diagram_expand(DiagramId d, TermVarId *q_slot) { Diagram *p = DG(d); if (q_slot) *q_slot = p->q_slot; return p->expand; }

/* the declaration checks with diagnostics: the context, each node's type at
 * its level, its term, its variables' declarations, the output (terminal).
 * Along the right fold these are the signature checks of zero and node at
 * the declaration's data, so the exported value has the diagram type. */
CheckStatus diagram_validate(DiagramId id, FaceId required, const char **reason) {
    Diagram *d = DG(id);
    CheckStatus st = check_context(d->params, reason);
    ContextId G = d->params;
    for (size_t k = 0; k < d->n && st == CK_VALID; k++) {
        const DiagNode *nd = &d->nodes[k];
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
            st = check_is_type(d->params, required, d->B, &lv, reason);
            if (st == CK_INVALID) *reason = "output type is not a type";
            else if (st == CK_VALID) st = check(G, required, d->o, d->B, reason);
        }
        if (st == CK_VALID && lv != d->lB) { *reason = "output/terminal type level annotation differs from its formation level"; st = CK_INVALID; }
    }
    return st;
}

/* ------------------------------------------------------------------ */
/* actions                                                               */

static CheckStatus face_in_context(ContextId G, FaceId phi, const char **reason) {
    Words dims; words_init(&dims); fc_dims(phi, &dims);
    for (size_t k = 0; k < dims.n; k++) if (!context_declares_dim(G, dims.w[k])) { words_free(&dims); *reason = "required face mentions an undeclared dimension"; return CK_INVALID; }
    words_free(&dims);
    return CK_VALID;
}
static CheckStatus type_at(ContextId G, FaceId req, RefId X, uint64_t l, const char *what, const char **reason) {
    uint64_t lv; CheckStatus st = check_is_type(G, req, X, &lv, reason);
    if (st != CK_VALID) { if (st == CK_INVALID) *reason = what; return st; }
    if (lv != l) { *reason = "universe level annotation differs from the formation level"; return CK_INVALID; }
    return CK_VALID;
}
/* The instance is the recipe's open body at the declaration's data. A
 * recipe is a fixed program of the library (like the §52 templates): its
 * closed function is checked at its type by the acceptance suite
 * (tests/test_runtime.c). An instance is typed by its signature: every
 * datum has been checked at its formal's instantiated type by the
 * declaration checks that precede (the diagrams by their node checks, which
 * are the node recipe's signature checks along the fold; the evidence; the
 * types and terms), so the instance's type is the recipe's type at the data;
 * it is compared by conversion with the declared Maps(domain, codomain).
 * Nothing evaluates the evidence (§88.1: a well-typed partial program
 * remains a program). Mathematical use is the separate proof-use judgment
 * of the applied recipe, which checks the closed function itself. */
static CheckStatus finish(Action *out, const Recipe *r, const RefId *args, const char **reason) {
    out->maps = rt_inst(r, args); out->applied = rt_apply(r, args);
    ConvStatus cv = convert_type(out->parameters, out->required_face, rt_inst_type(r, args), rt_maps_type(out->domain_level, out->codomain_level, out->domain, out->codomain));
    if (cv == CV_UNEQUAL) { *reason = "the instantiated action's type differs from Maps(domain, codomain)"; return CK_INVALID; }
    if (cv == CV_UNRESOLVED) { *reason = "unresolved: the instantiated action's type conversion"; return CK_UNRESOLVED; }
    return CK_VALID;
}

CheckStatus compile_identity(const IdentityDecl *d, Action *out, const char **reason) {
    ensure_init();
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(d->parameters, reason);
    if (st != CK_VALID) return st;
    if ((st = face_in_context(d->parameters, d->required_face, reason)) != CK_VALID) return st;
    if ((st = type_at(d->parameters, d->required_face, d->result_type, d->result_level, "result type is not a type", reason)) != CK_VALID) return st;
    Diagram *L = DG(d->left), *R = DG(d->right);
    if (L->params != d->parameters || R->params != d->parameters) { *reason = "diagram parameter context differs from the declaration's"; return CK_INVALID; }
    if (L->residual || R->residual) { *reason = "an identity declaration takes ordinary diagrams"; return CK_INVALID; }
    if (L->B != d->result_type || R->B != d->result_type || L->lB != d->result_level || R->lB != d->result_level) { *reason = "diagram output type differs from the result type"; return CK_INVALID; }
    if ((st = diagram_validate(d->left, d->required_face, reason)) != CK_VALID) return st;
    if ((st = diagram_validate(d->right, d->required_face, reason)) != CK_VALID) return st;
    RefId PT = mk_path_const(d->result_level, d->result_type, L->C, R->C);
    st = check(d->parameters, d->required_face, d->evidence, PT, reason);
    if (st != CK_VALID) { if (st == CK_INVALID) *reason = "evidence is not a path between the canonical values"; return st; }
    require(L->y == R->y, "diagrams over one parameter context and output type share their output point");
    out->kind = EV_IDENTITY;
    out->y = L->y;
    out->parameters = context_extend_term(d->parameters, L->y, d->result_type);
    out->required_face = d->required_face;
    out->domain = L->R[0]; out->codomain = R->R[0];
    out->domain_level = L->RL[0]; out->codomain_level = R->RL[0];
    RefId a[5] = { d->result_type, L->value, R->value, d->evidence, ref_var(L->y) };
    out->evidence = d->evidence; out->evidence_type = PT;
    return finish(out, rt_recipe(RK_ACTION, d->result_level, L->RL[0], R->RL[0], 0), a, reason);
}

CheckStatus compile_equivalence(ContextId params, FaceId req, RefId X, uint64_t lX, RefId Y, uint64_t lY, RefId e, Action *out, const char **reason) {
    ensure_init();
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    if ((st = face_in_context(params, req, reason)) != CK_VALID) return st;
    if ((st = type_at(params, req, X, lX, "X is not a type", reason)) != CK_VALID) return st;
    if ((st = type_at(params, req, Y, lY, "Y is not a type", reason)) != CK_VALID) return st;
    RefId ET = mk_equiv(lX, lY, X, Y);
    st = check(params, req, e, ET, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "e is not an equivalence X ≃ Y"; return st; }
    out->kind = EV_EQUIVALENCE; out->parameters = params; out->required_face = req;
    out->domain = X; out->codomain = Y; out->domain_level = lX; out->codomain_level = lY;
    RefId a[3] = { X, Y, e };
    out->evidence = e; out->evidence_type = ET;
    return finish(out, rt_recipe(RK_EQUIV_MAPS, lX, lY, 0, 0), a, reason);
}

CheckStatus compile_residual_equivalence(ContextId params, FaceId req, DiagramId Ld, DiagramId Rd, RefId e, Action *out, const char **reason) {
    ensure_init();
    memset(out, 0, sizeof *out);
    Diagram *L = DG(Ld), *R = DG(Rd);
    if (!L->residual || !R->residual) { *reason = "a residual equivalence takes residual descriptions"; return CK_INVALID; }
    if (L->params != params || R->params != params) { *reason = "description parameter context differs"; return CK_INVALID; }
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    if ((st = face_in_context(params, req, reason)) != CK_VALID) return st;
    if ((st = diagram_validate(Ld, req, reason)) != CK_VALID) return st;
    if ((st = diagram_validate(Rd, req, reason)) != CK_VALID) return st;
    RefId ET = mk_equiv(L->lB, R->lB, L->C, R->C);
    st = check(params, req, e, ET, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "e is not an equivalence between the terminal types"; return st; }
    out->kind = EV_RESIDUAL_EQUIVALENCE; out->parameters = params; out->required_face = req;
    out->domain = L->R[0]; out->codomain = R->R[0]; out->domain_level = L->RL[0]; out->codomain_level = R->RL[0];
    RefId a[3] = { L->value, R->value, e };
    out->evidence = e; out->evidence_type = ET;
    return finish(out, rt_recipe(RK_RES_ACTION, L->lB, L->RL[0], R->lB, R->RL[0]), a, reason);
}

/* Cut(C,D) = Σ(z:B). Σ(u : C=z). (D=z) */
static RefId cut_type(uint64_t lB, RefId B, RefId C, RefId D) {
    TermVarId z = keyed2(ROLE_CUT_Z, C, B);
    RefId Cz = mk_path_const(lB, B, C, ref_var(z)), Dz = mk_path_const(lB, B, D, ref_var(z));
    TermVarId u = keyed2(ROLE_CUT_U, D, Cz);
    return mk_sigma_lv(lB, lB, z, B, mk_sigma_lv(lB, lB, u, Cz, Dz));
}
CheckStatus compile_cut(ContextId params, FaceId req, RefId B, uint64_t lB, RefId C, RefId D, Action *out, const char **reason) {
    ensure_init();
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    if ((st = face_in_context(params, req, reason)) != CK_VALID) return st;
    if ((st = type_at(params, req, B, lB, "B is not a type", reason)) != CK_VALID) return st;
    st = check(params, req, C, B, reason); if (st != CK_VALID) return st;
    st = check(params, req, D, B, reason); if (st != CK_VALID) return st;
    out->kind = EV_CUT; out->parameters = params; out->required_face = req;
    out->domain = cut_type(lB, B, C, D); out->codomain = mk_path_const(lB, B, C, D);
    out->domain_level = lB; out->codomain_level = lB;
    RefId a[3] = { B, C, D };
    return finish(out, rt_recipe(RK_CUT_MAPS, lB, 0, 0, 0), a, reason);
}

CheckStatus compile_contractible_fibre(ContextId params, FaceId req, RefId B, uint64_t lB, RefId R, RefId k, Action *out, const char **reason) {
    ensure_init();
    memset(out, 0, sizeof *out);
    CheckStatus st = check_context(params, reason); if (st != CK_VALID) return st;
    if ((st = face_in_context(params, req, reason)) != CK_VALID) return st;
    if ((st = type_at(params, req, B, lB, "B is not a type", reason)) != CK_VALID) return st;
    TermVarId bb = keyed2(ROLE_CF_BIND, R, B);
    ContextId Gb = context_extend_term(params, bb, B);
    uint64_t lR;
    st = check_is_type(Gb, req, mk_app(R, ref_var(bb)), &lR, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "R(b) is not a type"; return st; }
    RefId Kt = mk_pi_lv(lB, lR, bb, B, mk_contr(lR, mk_app(R, ref_var(bb))));
    st = check(params, req, k, Kt, reason); if (st != CK_VALID) { if (st == CK_INVALID) *reason = "k is not a pointwise contraction of R"; return st; }
    out->kind = EV_CONTRACTIBLE_FIBRE; out->parameters = params; out->required_face = req;
    out->domain = mk_sigma_lv(lB, lR, bb, B, mk_app(R, ref_var(bb))); out->codomain = B;
    out->domain_level = level_max(lB, lR); out->codomain_level = lB;
    RefId a[3] = { B, R, k };
    out->evidence = k; out->evidence_type = Kt;
    return finish(out, rt_recipe(RK_FIBRE_MAPS, lB, lR, 0, 0), a, reason);
}

/* ------------------------------------------------------------------ */
/* invocation: ordinary application                                      */

RefId action_function(const Action *a, int dir) { return dir ? rt_d(a->maps) : rt_c(a->maps); }
RefId action_call(const Action *a, int dir, MapId sigma, RefId arg) { return mk_app(reindex(action_function(a, dir), sigma), arg); }

ProofUse action_proof_use(const Action *a) { return proof_use(a->parameters, a->required_face, a->applied, rt_maps_type(a->domain_level, a->codomain_level, a->domain, a->codomain)); }
