#include "lib.h"

/* Fresh names for the derived definitions are minted deterministically from
 * the references they must be fresh for (they are created after those
 * references exist, so no image can contain them). Identical invocations
 * therefore intern to identical references. */
enum {
    N_FILL = 1, N_PATHC, N_REFL, N_REV, N_CONCAT_I, N_CONCAT_J, N_FUN, N_CONTR_C, N_CONTR_X,
    N_FIB_X, N_EQ_F, N_EQ_Y, N_ID_X, N_IDEQ_Y, N_IDEQ_W, N_IDEQ_I, N_IDEQ_J, N_EXT, N_UA,
    N_CPI_X1, N_CPI_RHO, N_CPI_J, N_CSG_RHO, N_CPA_J, N_CU_J,
    N_CG_RHO, N_CG_Q, N_CG_Q2
};

/* kind signature of each tag's payload slots: R ref, F face, I interval, D dim, C constant */
static const char *key_sig(uint64_t tag) {
    switch (tag) {
    case N_FILL: return "RFRRID";
    case N_EXT: return "RRRFRC";
    case N_CPI_X1: case N_CPI_RHO: case N_CPI_J: case N_CSG_RHO: case N_CPA_J: case N_CU_J:
    case N_CG_RHO: case N_CG_Q: case N_CG_Q2: return "RFRRDC";
    default: return "RRRRRR";       /* refs; unused slots are 0 and recorded as constants */
    }
}
static size_t typed_key(uint64_t tag, const uint64_t *vals, KeyWord *out) {
    const char *sig = key_sig(tag);
    out[0].kind = KW_CONST; out[0].v = tag;
    for (size_t k = 0; k < 6; k++) {
        KeyKind kind = KW_CONST;
        if (vals[k] != 0) switch (sig[k]) {
            case 'R': kind = KW_REF; break; case 'F': kind = KW_FACE; break;
            case 'I': kind = KW_INTERVAL; break; case 'D': kind = KW_DIM; break; default: kind = KW_CONST;
        }
        out[k + 1].kind = kind; out[k + 1].v = vals[k];
    }
    return 7;
}
static DimVarId kdim6(uint64_t tag, uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e, uint64_t f) {
    uint64_t vals[6] = { a, b, c, d, e, f }; KeyWord key[7];
    return fresh_dim_keyed(key, typed_key(tag, vals, key));
}
#define kdim(tag, a, b, c, d, e) kdim6(tag, a, b, c, d, e, 0)
static TermVarId kterm(uint64_t tag, uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e, RefId type) {
    uint64_t vals[6] = { a, b, c, d, e, 0 }; KeyWord key[7];
    return fresh_term_keyed(key, typed_key(tag, vals, key), type);
}

IntervalId iv_line(IntervalId r, IntervalId s, DimVarId j) {
    IntervalId vj = iv_var(j);
    return iv_join(iv_meet(r, iv_negate(vj)), iv_meet(s, vj));
}

static RefId empty_system(void) { return mk_system(0, NULL, NULL); }

RefId mk_fill(DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId a0, IntervalId r) {
    /* fill^i A_i [phi ↦ u_i] a0 (r) = comp^j A_{r∧j} [phi ↦ u_{r∧j}, (r=0) ↦ a0] a0 */
    DimVarId j = kdim6(N_FILL, A_i, phi, u_i, a0, r, i);
    IntervalId rj = iv_meet(r, iv_var(j));
    RefId A = reindex_dim(A_i, i, rj);
    RefId u = reindex_dim(u_i, i, rj);
    FaceId r0 = fc_endpoint(r, 0);
    FaceId faces[2] = { phi, r0 };
    RefId terms[2] = { u, a0 };
    return mk_comp(j, A, fc_join(phi, r0), mk_system(2, faces, terms), a0);
}

RefId mk_hcomp(DimVarId j, RefId X, FaceId phi, RefId u_j, RefId cap) { return mk_comp(j, X, phi, u_j, cap); }

RefId mk_coe(DimVarId i, RefId A_i, RefId a0) { return mk_comp(i, A_i, fc_false(), empty_system(), a0); }

RefId mk_path_const(RefId A, RefId l, RefId r) { return mk_path(kdim(N_PATHC, A, 0, 0, 0, 0), A, l, r); }
RefId mk_refl(RefId A, RefId a) { return mk_plam(kdim(N_REFL, A, a, 0, 0, 0), a); }
RefId mk_papp_const(RefId A, RefId l, RefId r, RefId p, IntervalId s) { return mk_papp(kdim(N_PATHC, A, 0, 0, 0, 0), A, l, r, p, s); }

RefId mk_path_rev(RefId A, RefId l, RefId r, RefId p) {
    DimVarId i = kdim(N_REV, A, p, 0, 0, 0);
    return mk_plam(i, mk_papp_const(A, l, r, p, iv_negate(iv_var(i))));
}

RefId mk_path_concat(RefId A, RefId x, RefId y, RefId z, RefId p, RefId q) {
    /* p·q = ⟨i⟩ hcomp^j_A [(i=0) ↦ x, (i=1) ↦ q(j)] p(i) */
    DimVarId i = kdim(N_CONCAT_I, A, p, q, 0, 0);
    DimVarId j = kdim(N_CONCAT_J, A, p, q, 0, 0);
    FaceId faces[2] = { fc_lit(i, 0), fc_lit(i, 1) };
    RefId terms[2] = { x, mk_papp_const(A, y, z, q, iv_var(j)) };
    RefId tube = mk_system(2, faces, terms);
    RefId body = mk_hcomp(j, A, fc_join(faces[0], faces[1]), tube, mk_papp_const(A, x, y, p, iv_var(i)));
    return mk_plam(i, body);
}

/* ---- equivalence data ---- */

RefId mk_fun(RefId X, RefId Y) {
    TermVarId x = kterm(N_FUN, X, Y, 0, 0, 0, X);
    return mk_pi(x, X, Y);
}

RefId mk_contr(RefId X) {
    TermVarId c = kterm(N_CONTR_C, X, 0, 0, 0, 0, X);
    TermVarId x = kterm(N_CONTR_X, X, 0, 0, 0, 0, X);
    return mk_sigma(c, X, mk_pi(x, X, mk_path_const(X, ref_var(c), ref_var(x))));
}

RefId mk_fib(RefId X, RefId Y, RefId f, RefId y) {
    TermVarId x = kterm(N_FIB_X, X, Y, f, y, 0, X);
    return mk_sigma(x, X, mk_path_const(Y, mk_app(f, ref_var(x)), y));
}

RefId mk_equiv(RefId X, RefId Y) {
    RefId XY = mk_fun(X, Y);
    TermVarId f = kterm(N_EQ_F, X, Y, 0, 0, 0, XY);
    TermVarId y = kterm(N_EQ_Y, X, Y, 0, 0, 0, Y);
    return mk_sigma(f, XY, mk_pi(y, Y, mk_contr(mk_fib(X, Y, ref_var(f), ref_var(y)))));
}

RefId mk_id_fun(RefId X) {
    TermVarId x = kterm(N_ID_X, X, 0, 0, 0, 0, X);
    return mk_lam(x, X, ref_var(x));
}

RefId mk_id_equiv(RefId X) {
    /* (id, λy. ((y, refl), λw. ⟨i⟩ (p(¬i), ⟨j⟩ p(¬i ∨ j))))  with (x,p) = w */
    RefId idf = mk_id_fun(X);
    TermVarId y = kterm(N_IDEQ_Y, X, 0, 0, 0, 0, X);
    RefId fib = mk_fib(X, X, idf, ref_var(y));
    TermVarId w = kterm(N_IDEQ_W, X, 0, 0, 0, 0, fib);
    RefId xw = mk_fst(ref_var(w)), p = mk_snd(ref_var(w));
    RefId idx = mk_app(idf, xw);                 /* f x, as the fibre type states it */
    DimVarId i = kdim(N_IDEQ_I, X, 0, 0, 0, 0), j = kdim(N_IDEQ_J, X, 0, 0, 0, 0);
    IntervalId ni = iv_negate(iv_var(i));
    RefId first = mk_papp_const(X, idx, ref_var(y), p, ni);
    RefId second = mk_plam(j, mk_papp_const(X, idx, ref_var(y), p, iv_join(ni, iv_var(j))));
    RefId contraction = mk_lam(w, fib, mk_plam(i, mk_pair(first, second)));
    RefId centre = mk_pair(ref_var(y), mk_refl(X, ref_var(y)));
    return mk_pair(idf, mk_lam(y, X, mk_pair(centre, contraction)));
}

RefId equiv_map(RefId e) { return mk_fst(e); }
RefId equiv_contr(RefId e, RefId y) { return mk_app(mk_snd(e), y); }

RefId mk_extend_contr(RefId X, RefId c, RefId k, FaceId theta, RefId v) {
    /* hcomp^j_X [theta ↦ k(v)@j] c */
    DimVarId j = kdim(N_EXT, X, c, k, theta, v);
    RefId tube = mk_papp_const(X, c, v, mk_app(k, v), iv_var(j));
    return mk_hcomp(j, X, theta, tube, c);
}

RefId mk_line_equiv(DimVarId j, RefId X_j) {
    RefId X0 = reindex_dim(X_j, j, iv_zero());
    return mk_coe(j, mk_equiv(X0, X_j), mk_id_equiv(X0));
}

RefId mk_ua(RefId X, RefId Y, RefId e) {
    DimVarId i = kdim(N_UA, X, Y, e, 0, 0);
    FaceId faces[2] = { fc_lit(i, 0), fc_lit(i, 1) };
    RefId Ts[2] = { X, Y };
    RefId es[2] = { e, mk_id_equiv(Y) };
    return mk_plam(i, mk_glue_type(Y, fc_join(faces[0], faces[1]), mk_system(2, faces, Ts), mk_system(2, faces, es)));
}

/* ---- structural composition clauses (§14, §16, §17) ---- */

RefId comp_clause_pi(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    Head h; open_ref(fam, &h);
    require(h.tag == T_PI, "pi clause on a non-pi head");
    RefId D_i = h.f[0].id;
    head_free(&h);
    RefId D_1 = reindex_dim(D_i, i, iv_one());
    TermVarId x1 = kterm(N_CPI_X1, fam, phi, u_i, cap, i, D_1);
    DimVarId rho = kdim(N_CPI_RHO, fam, phi, u_i, cap, i);
    DimVarId jj = kdim(N_CPI_J, fam, phi, u_i, cap, i);
    /* shared backward filler v(r) = fill^j D_{¬j} [] x1 (¬r), built once with r = rho */
    RefId D_negj = reindex_dim(D_i, i, iv_negate(iv_var(jj)));
    RefId V = mk_fill(jj, D_negj, fc_false(), empty_system(), ref_var(x1), iv_negate(iv_var(rho)));
    RefId v_i = reindex_dim(V, rho, iv_var(i));
    RefId v_0 = reindex_dim(V, rho, iv_zero());
    RefId E_i = apply_term_binder(fam, 0, 1, v_i);          /* E_i(v(i)), i free */
    RefId body = mk_comp(i, E_i, phi, mk_app(u_i, v_i), mk_app(cap, v_0));
    return mk_lam(x1, D_1, body);
}

RefId comp_clause_sigma(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    Head h; open_ref(fam, &h);
    require(h.tag == T_SIGMA, "sigma clause on a non-sigma head");
    RefId D_i = h.f[0].id;
    head_free(&h);
    DimVarId rho = kdim(N_CSG_RHO, fam, phi, u_i, cap, i);
    RefId A = mk_fill(i, D_i, phi, mk_fst(u_i), mk_fst(cap), iv_var(rho));   /* a(rho), one reference */
    RefId a_i = reindex_dim(A, rho, iv_var(i));
    RefId a_1 = reindex_dim(A, rho, iv_one());
    RefId E_i = apply_term_binder(fam, 0, 1, a_i);
    RefId b_1 = mk_comp(i, E_i, phi, mk_snd(u_i), mk_snd(cap));
    return mk_pair(a_1, b_1);
}

RefId comp_clause_path(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    Head h; open_ref(fam, &h);
    require(h.tag == T_PATH, "path clause on a non-path head");
    RefId l_i = h.f[1].id, r_i = h.f[2].id;
    head_free(&h);
    DimOpen B = resolve_dim_binder(fam, 0, 0);               /* B(i, k), formal k = B.j */
    DimVarId j = kdim(N_CPA_J, fam, phi, u_i, cap, i);
    RefId B_ij = reindex_dim(B.body, B.j, iv_var(j));
    RefId u_at_j = mk_papp(B.j, B.body, l_i, r_i, u_i, iv_var(j));
    /* the cap lives at i = 0 */
    RefId B0 = reindex_dim(B.body, i, iv_zero());
    RefId cap_at_j = mk_papp(B.j, B0, reindex_dim(l_i, i, iv_zero()), reindex_dim(r_i, i, iv_zero()), cap, iv_var(j));
    FaceId faces[3] = { phi, fc_lit(j, 0), fc_lit(j, 1) };
    RefId terms[3] = { u_at_j, l_i, r_i };
    FaceId face = fc_join(phi, fc_join(faces[1], faces[2]));
    RefId body = mk_comp(i, B_ij, face, mk_system(3, faces, terms), cap_at_j);
    return mk_plam(j, body);
}

RefId comp_clause_universe(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    Head h; open_ref(fam, &h);
    require(h.tag == T_UNIVERSE, "universe clause on a non-universe head");
    head_free(&h);
    /* comp^i U [phi ↦ U_i] A_0 → Glue [phi ↦ (U_1, LineEquiv(j ↦ U_{¬j}))] A_0 */
    RefId U_1 = reindex_dim(u_i, i, iv_one());
    DimVarId j = kdim(N_CU_J, fam, phi, u_i, cap, i);
    RefId X_j = reindex_dim(u_i, i, iv_negate(iv_var(j)));
    return mk_glue_type(cap, phi, U_1, mk_line_equiv(j, X_j));
}

RefId comp_clause_glue(DimVarId i, RefId fam, FaceId psi, RefId u_i, RefId u_0) {
    Head h; open_ref(fam, &h);
    require(h.tag == T_GLUE_TYPE, "glue clause on a non-glue head");
    RefId A_i = h.f[0].id; FaceId alpha_i = h.f[1].id; RefId T_i = h.f[2].id, e_i = h.f[3].id;
    head_free(&h);
    IntervalId zero = iv_zero(), one = iv_one();
    RefId A_0 = reindex_dim(A_i, i, zero), T_0 = reindex_dim(T_i, i, zero), e_0 = reindex_dim(e_i, i, zero);
    FaceId alpha_0 = fc_reindex(alpha_i, map_single_dim(i, zero));
    RefId A_1 = reindex_dim(A_i, i, one), T_1 = reindex_dim(T_i, i, one), e_1 = reindex_dim(e_i, i, one);
    FaceId alpha_1 = fc_reindex(alpha_i, map_single_dim(i, one));
    RefId u_1 = reindex_dim(u_i, i, one);

    /* base filler */
    RefId a0 = mk_unglue(A_0, alpha_0, T_0, e_0, u_0);
    RefId ungl_i = mk_unglue(A_i, alpha_i, T_i, e_i, u_i);
    DimVarId rho = kdim(N_CG_RHO, fam, psi, u_i, u_0, i);
    RefId Afill = mk_fill(i, A_i, psi, ungl_i, a0, iv_var(rho));
    RefId a_i = reindex_dim(Afill, rho, iv_var(i));
    RefId a1 = reindex_dim(Afill, rho, one);

    /* on delta = ∀i alpha_i the fibre line is available: the constructions
     * below are declared partial on delta (§2 required_face annotation) */
    FaceId delta = fc_forall(i, alpha_i);
    RefId f_i = equiv_map(e_i), f_1 = equiv_map(e_1);      /* partial on alpha_i / alpha_1 by their own data */
    term_require_push(delta);
    RefId Tfill = mk_fill(i, T_i, psi, u_i, u_0, iv_var(rho));
    RefId t_i = reindex_dim(Tfill, rho, iv_var(i));
    RefId t1p = reindex_dim(Tfill, rho, one);
    DimVarId q = kdim(N_CG_Q, fam, psi, u_i, u_0, i);
    FaceId wf[3] = { psi, fc_lit(q, 0), fc_lit(q, 1) };
    RefId wt[3] = { a_i, mk_app(f_i, t_i), a_i };
    RefId omega_q = mk_comp(i, A_i, fc_join(psi, fc_join(wf[1], wf[2])), mk_system(3, wf, wt), a0);
    RefId omega = mk_plam(q, omega_q);                      /* f_1(t1') = a1 */
    term_require_pop();

    /* under alpha_1: extend [delta ↦ (t1', omega), psi ↦ (u_1, refl)] in fib(f_1, a1) */
    term_require_push(alpha_1);
    RefId fibT = mk_fib(T_1, A_1, f_1, a1);
    FaceId pf[2] = { delta, psi };
    RefId pt[2] = { mk_pair(t1p, omega), mk_pair(u_1, mk_refl(A_1, a1)) };
    RefId P = mk_system(2, pf, pt);
    RefId C = equiv_contr(e_1, a1);
    RefId ext = mk_extend_contr(fibT, mk_fst(C), mk_snd(C), fc_join(delta, psi), P);
    RefId t1 = mk_fst(ext), p = mk_snd(ext);                /* p : f_1(t1) = a1 */
    term_require_pop();

    /* repair the base endpoint */
    DimVarId q2 = kdim(N_CG_Q2, fam, psi, u_i, u_0, i);
    FaceId rf[2] = { alpha_1, psi };
    RefId rt[2] = { mk_papp_const(A_1, mk_app(f_1, t1), a1, p, iv_negate(iv_var(q2))), a1 };
    RefId a1p = mk_hcomp(q2, A_1, fc_join(alpha_1, psi), mk_system(2, rf, rt), a1);
    return mk_glue_intro(A_1, alpha_1, T_1, e_1, t1, a1p);
}
