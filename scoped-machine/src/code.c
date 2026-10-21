/* code.c — the records the machine runs, as values of the language.
 *
 * A code is a record former applied to a record: (quote t) holds a term
 * record, (qiv r) an interval record, (qfc φ) a face record, (qlv l) a
 * level. Nothing else is a representation of syntax: the record a quote
 * holds is the record the machine evaluates. Each code eliminator is one
 * native rule over those records; its value is a reduct term the evaluator
 * then observes.
 *
 *   cmatch[f](c, h, d)    the former of c is f (0: a variable;
 *                         FORMER_IVCODE/FCCODE/LVCODE: an interval, face or
 *                         level code): h applied
 *                         to c's fields as codes, a field under a binder as
 *                         the function λ(a:Code). cinst[k](c, a); otherwise
 *                         d. A system with branches (φ, t)·rest is matched
 *                         by T_SYSTEM with fields (qfc φ) (quote t) (quote
 *                         rest); the empty system by FORMER_SYS0. An
 *                         absent optional field is given as (qlv none)
 *   cinst[k](c, a)        the field k of c opened at the term or interval a
 *   cset[k](c, d)         c with its field k replaced by the code d
 *   csetb[k](c, d)        c with its field k, under a binder, replaced by
 *                         d applied to the code of the binder's variable
 *   cmtype(m, X)          for the code m of a cmatch: the type of its
 *                         handler — the former's fields as codes (a field
 *                         under a binder as Code → Code), then X
 *   clevels(c, h)         h applied to the level codes of c's annotation (a
 *                         universe: its level, then none)
 *   csetlv(c, l, m)       c with the annotation l, m
 *   clsucc(l), clmax(l,m) successor and maximum of level codes
 *   cop[o](a, b)          ¬a, a∧b, a∨b on interval codes; φ∧ψ, φ∨ψ on face
 *                         codes; ∀a.ψ for the code a of a dimension variable
 *   csyscons(φ, t, s)     the system s with the branch φ ↦ t in front
 *   csubst(c, v, a)       c with the variable whose code is v replaced by a
 *   ctype(c)              the declared type of the variable or defined
 *                         symbol c
 *   cvar(c)               the code of the variable of c's binder (the name
 *                         the machine opens c's fields at)
 *   ceq(a, b, t, f)       t when a and b are one record, otherwise f
 *   cent(a, b, t, f)      t when the face a entails the face b, otherwise f
 *   cfcend[ε](r)          the face (r = ε)
 *   cunfold(c, h, d)      h applied to the code of the body of the defined
 *                         symbol c; d when c is no symbol with a body
 *
 * F_CODE(t, χ) is the reduct of the code eliminator t under χ, as the
 * record RQ(kind, word): kind 0 the reduct `word`, 1 neutral (an operand
 * is no code introduction), 2 an operand's observation `word` (no
 * observation or invalid), 3 an operand of the wrong kind. */
#include "eval.h"
#include "template.h"
#include "interval.h"
#include "scope.h"

typedef struct {
    Tag tag, ct, bt, xt; uint64_t payload, c, x, b, y, res, h, code, var, img, fv, l1, l2, npay, nlev;
    size_t nf, q, rk; uint64_t ids[6]; Sort bs; WordBuf wb;
} CdLoc;
#define RES(id) res_get(id)
#define NO_REPL ((size_t)-1)
static bool is_code(Tag t) { return t == T_QUOTE || t == T_QIV || t == T_QFC || t == T_QLV; }
static Tag code_of_kind(uint64_t kind) { return kind == F_REF ? T_QUOTE : kind == F_INTERVAL ? T_QIV : T_QFC; }

/* observe the code `src`: its introduction into dst (tag dt), or finish */
#define OBS_CODE(dst, dt, src) FR_AWAIT(k, L->res, F_OBS, (src), observe_key(chi, 0)); \
    if (RES(L->res).cls == R_NO_OBSERVATION || RES(L->res).cls == R_INVALID) FR_FINISH(k, RQ(2, L->res)); \
    if (RES(L->res).cls != R_INTRODUCTION) FR_FINISH(k, RQ(1, 0)); \
    (dst) = RES(L->res).ref; (dt) = ref_tag(dst); \
    if (!is_code(dt)) FR_FINISH(k, RQ(3, 0))
/* the record a code holds (a level code: its level) */
#define CODE_PAYLOAD(dst, c, ct) FR_AWAIT(k, dst, (ct) == T_QLV ? F_HEAD : F_FIELD, (c), 0)

static void code_step(Cont *k, uint64_t v) {
    CdLoc *L = FR_LOC(k, CdLoc);
    RefId t = k->w[0]; FaceId chi = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    L->tag = ref_tag(t);
    FR_AWAIT(k, L->payload, F_HEAD, t, 0);
    FR_AWAIT(k, L->c, F_FIELD, t, 0);
    OBS_CODE(L->c, L->ct, L->c);
    CODE_PAYLOAD(L->x, L->c, L->ct);

    if (L->tag == T_CEQ || L->tag == T_CENT || L->tag == T_CLMAX) {
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        OBS_CODE(L->b, L->bt, L->b);
        CODE_PAYLOAD(L->y, L->b, L->bt);
        if (L->tag == T_CLMAX) {
            if (L->ct != T_QLV || L->bt != T_QLV) FR_FINISH(k, RQ(3, 0));
            FR_LMAX(k, r, L->x, L->y);
            FR_CALL(k, r, mk_tag_sub(k, T_QLV, r, LEVELS_NONE, 0, NULL, 0));
            FR_FINISH(k, RQ(0, r));
        }
        if (L->tag == T_CEQ) r = L->ct == L->bt && L->x == L->y;
        else {
            if (L->ct != T_QFC || L->bt != T_QFC) FR_FINISH(k, RQ(3, 0));
            FR_AWAIT(k, r, F_FCENT, L->x, L->y);
            r = r == 2;
        }
        FR_AWAIT(k, r, F_FIELD, t, r ? 2 : 3);
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_COP) {
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        OBS_CODE(L->b, L->bt, L->b);
        CODE_PAYLOAD(L->y, L->b, L->bt);
        if (L->payload <= COP_IVOR) {
            if (L->ct != T_QIV || L->bt != T_QIV) FR_FINISH(k, RQ(3, 0));
            if (L->payload == COP_IVNEG) FR_AWAIT(k, r, F_IVNEG, L->x, 0);
            else if (L->payload == COP_IVAND) FR_AWAIT(k, r, F_IVMEET, L->x, L->y);
            else FR_AWAIT(k, r, F_JOIN, L->x, L->y);
            FR_CALL(k, r, MK_SUB(k, T_QIV, 0, LEVELS_NONE, 0, r));
            FR_FINISH(k, RQ(0, r));
        }
        if (L->payload == COP_FORALL) {
            /* ∀ over the dimension variable a: its interval is one positive atom */
            size_t n; const uint64_t *w = L->ct == T_QIV ? rget(L->x, &n) : NULL;
            if (!w || n != 2 || w[1] != DNF_SEP || IV_ATOM_NEG(w[0]) || L->bt != T_QFC) FR_FINISH(k, RQ(3, 0));
            FR_AWAIT(k, r, F_FCFORALL, L->y, IV_ATOM_DIM(w[0]));
        } else {
            if (L->ct != T_QFC || L->bt != T_QFC) FR_FINISH(k, RQ(3, 0));
            if (L->payload == COP_FCAND) FR_AWAIT(k, r, F_FCMEET, L->x, L->y);
            else FR_AWAIT(k, r, F_JOIN, L->x, L->y);
        }
        FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CSYSCONS) {
        if (L->ct != T_QFC) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        OBS_CODE(L->b, L->bt, L->b);
        if (L->bt != T_QUOTE) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->y, F_FIELD, L->b, 0);
        FR_AWAIT(k, L->b, F_FIELD, t, 2);
        OBS_CODE(L->b, L->bt, L->b);
        if (L->bt != T_QUOTE) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->h, F_FIELD, L->b, 0);
        if (ref_is_var(L->h) || ref_tag(L->h) != T_SYSTEM) FR_FINISH(k, RQ(3, 0));
        L->nf = tnode_nfields(ref_tnode(L->h));
        creq_system_begin(&L->wb, L->nf / 2 + 1);
        creq_system_branch(&L->wb, L->x, L->y);
        for (L->q = 0; L->q < L->nf; L->q += 2) {
            FR_AWAIT(k, L->y, F_FIELD, L->h, L->q);
            FR_AWAIT(k, r, F_FIELD, L->h, L->q + 1);
            creq_system_branch(&L->wb, L->y, r);
        }
        wordbuf_push(&L->wb, 0);
        FR_CALL(k, r, creq_buf(k, &L->wb));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CSUBST) {
        /* v: the code of a variable (a term variable, or one positive atom) */
        if (L->ct == T_QLV) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        OBS_CODE(L->b, L->bt, L->b);
        FR_AWAIT(k, L->y, F_FIELD, L->b, 0);
        FR_AWAIT(k, L->h, F_FIELD, t, 2);
        OBS_CODE(L->h, L->xt, L->h);
        FR_AWAIT(k, L->fv, F_FIELD, L->h, 0);
        if (L->bt == T_QUOTE && L->xt == T_QUOTE && ref_is_var(L->y)) L->y = map_single_term(ref_var_id(L->y), L->fv);
        else if (L->bt == T_QIV && L->xt == T_QIV) {
            size_t n; const uint64_t *w = rget(L->y, &n);
            if (n != 2 || w[1] != DNF_SEP || IV_ATOM_NEG(w[0])) FR_FINISH(k, RQ(3, 0));
            L->y = map_single_dim(IV_ATOM_DIM(w[0]), L->fv);
        } else FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, r, L->ct == T_QUOTE ? F_TREF : L->ct == T_QIV ? F_TIV : F_TFC, L->x, re_key(L->y));
        FR_CALL(k, r, MK_SUB(k, L->ct, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CLSUCC) {
        if (L->ct != T_QLV) FR_FINISH(k, RQ(3, 0));
        FR_LSUCC(k, r, L->x);
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, r, LEVELS_NONE, 0, NULL, 0));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CFCEND) {
        if (L->ct != T_QIV) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, r, F_FCEND, L->x, L->payload);
        FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CMATCH) {
        L->xt = L->ct == T_QIV ? FORMER_IVCODE : L->ct == T_QFC ? FORMER_FCCODE : L->ct == T_QLV ? FORMER_LVCODE : ref_is_var(L->x) ? 0 : ref_tag(L->x);
        L->nf = L->ct == T_QUOTE && L->xt ? tnode_nfields(ref_tnode(L->x)) : 0;
        if (L->xt == T_SYSTEM && !L->nf) L->xt = FORMER_SYS0;
        if (L->xt != L->payload) { FR_AWAIT(k, r, F_FIELD, t, 2); FR_FINISH(k, RQ(0, r)); }
        FR_AWAIT(k, L->h, F_FIELD, t, 1);
        if (L->xt == T_SYSTEM) {
            /* the first branch and the rest */
            FR_AWAIT(k, r, F_FIELD, L->x, 0);
            FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
            FR_AWAIT(k, r, F_FIELD, L->x, 1);
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
            creq_system_begin(&L->wb, L->nf / 2 - 1);
            for (L->q = 2; L->q < L->nf; L->q += 2) {
                FR_AWAIT(k, L->y, F_FIELD, L->x, L->q);
                FR_AWAIT(k, r, F_FIELD, L->x, L->q + 1);
                creq_system_branch(&L->wb, L->y, r);
            }
            wordbuf_push(&L->wb, 0);
            FR_CALL(k, r, creq_buf(k, &L->wb));
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
            FR_FINISH(k, RQ(0, L->h));
        }
        if (L->ct != T_QUOTE || !L->xt) FR_FINISH(k, RQ(0, L->h));
        FR_CALL(k, L->code, mk_tag_sub(k, T_CODE, 0, LEVELS_NONE, 0, NULL, 0));
        for (L->q = 0; L->q < tag_schema(L->xt)->nf; L->q++) {
            if (L->q >= L->nf)      /* an absent optional field: the code (qlv none) */
                FR_CALL(k, L->fv, mk_tag_sub(k, T_QLV, LEVEL_NONE, LEVELS_NONE, 0, NULL, 0));
            else if (schema_slot(L->xt, L->q) != NO_SLOT) {
                /* a field under a binder: λ(a:Code). cinst[q](c, a), its
                 * variable named by this eliminator and the field */
                L->var = binder_term_var(t, (BinderSlot)L->q, L->code);
                FR_AWAIT(k, r, F_REFVAR, L->var, 0);
                FR_CALL(k, r, MK_SUB(k, T_CINST, L->q, LEVELS_NONE, 0, L->c, r));
                FR_CALL(k, L->fv, MK_SUB(k, T_LAM, 0, LEVELS_NONE, L->var, L->code, r));
            } else {
                FR_AWAIT(k, L->fv, F_FIELD, L->x, L->q);
                FR_CALL(k, L->fv, MK_SUB(k, code_of_kind(schema_kind(L->xt, L->q)), 0, LEVELS_NONE, 0, L->fv));
            }
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, L->fv));
        }
        FR_FINISH(k, RQ(0, L->h));
    }

    /* the remaining eliminators take the code of a term record */
    if (L->ct != T_QUOTE) FR_FINISH(k, RQ(3, 0));

    if (L->tag == T_CMTYPE) {
        /* m: the code of a cmatch; the handler type of its former */
        if (ref_is_var(L->x) || ref_tag(L->x) != T_CMATCH) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->npay, F_HEAD, L->x, 0);
        FR_AWAIT(k, L->h, F_FIELD, t, 1);                  /* X */
        OBS_CODE(L->b, L->bt, L->h);
        if (L->bt != T_QUOTE) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->h, F_FIELD, L->b, 0);
        FR_CALL(k, L->code, mk_tag_sub(k, T_CODE, 0, LEVELS_NONE, 0, NULL, 0));
        L->xt = (Tag)L->npay;
        L->nf = L->npay == T_SYSTEM ? 3 : (L->npay == 0 || L->npay >= FORMER_LVCODE) ? 0 : tag_schema(L->xt)->nf;
        for (L->q = L->nf; L->q-- > 0; ) {
            /* the field's argument type: Code, or Code → Code under a binder */
            L->fv = L->code;
            if (L->npay != T_SYSTEM && schema_slot(L->xt, L->q) != NO_SLOT) {
                L->var = binder_term_var(t, (BinderSlot)(100 + L->q), L->code);
                FR_CALL(k, L->fv, MK_SUB(k, T_PI, 0, LEVELS_NONE, L->var, L->code, L->code));
            }
            L->var = binder_term_var(t, (BinderSlot)L->q, L->fv);
            FR_CALL(k, L->h, MK_SUB(k, T_PI, 0, LEVELS_NONE, L->var, L->fv, L->h));
        }
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, L->h));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CTYPE) {
        if (ref_is_var(L->x)) FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, term_var_type(ref_var_id(L->x))));
        else {
            if (ref_tag(L->x) != T_GLOBAL) FR_FINISH(k, RQ(3, 0));
            FR_AWAIT(k, r, F_HEAD, L->x, 0);
            FR_AWAIT(k, r, F_UNFOLD, L->x, global_decl_type((SymbolId)r));
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        }
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CUNFOLD) {
        L->b = 0;
        if (!ref_is_var(L->x) && ref_tag(L->x) == T_GLOBAL) {
            FR_AWAIT(k, r, F_HEAD, L->x, 0);
            L->b = global_body_sealed((SymbolId)r);
        }
        if (!L->b) { FR_AWAIT(k, r, F_FIELD, t, 2); FR_FINISH(k, RQ(0, r)); }
        FR_AWAIT(k, r, F_UNFOLD, L->x, L->b);
        FR_CALL(k, L->y, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_AWAIT(k, L->h, F_FIELD, t, 1);
        FR_CALL(k, r, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, L->y));
        FR_FINISH(k, RQ(0, r));
    }

    if (ref_is_var(L->x)) FR_FINISH(k, RQ(3, 0));
    L->xt = ref_tag(L->x);
    L->nf = tnode_nfields(ref_tnode(L->x));
    L->bs = (Sort)tag_schema(L->xt)->bsort;
    FR_AWAIT(k, L->npay, F_HEAD, L->x, 0);
    FR_AWAIT(k, L->nlev, F_HEAD, L->x, 1);

    if (L->tag == T_CVAR) {
        if (!L->bs) FR_FINISH(k, RQ(3, 0));
        if (L->bs == S_DIM) FR_CALL(k, r, MK_SUB(k, T_QIV, 0, LEVELS_NONE, 0, iv_var(binder_dim_var(L->x, 0))));
        else {
            FR_AWAIT(k, L->y, F_FIELD, L->x, 0);
            FR_AWAIT(k, r, F_REFVAR, binder_term_var(L->x, 0, L->y), 0);
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        }
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CINST) {
        if (L->payload >= L->nf || schema_slot(L->xt, L->payload) == NO_SLOT) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        OBS_CODE(L->b, L->bt, L->b);
        if (L->bt != (L->bs == S_TERM ? T_QUOTE : T_QIV)) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->y, F_FIELD, L->b, 0);
        FR_AWAIT(k, r, F_BINDER, L->x, binder_req(L->bs, schema_slot(L->xt, L->payload), L->payload, L->y));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CLEVELS) {
        if (L->xt == T_UNIVERSE) { L->l1 = L->npay; L->l2 = LEVEL_NONE; }
        else { L->l1 = levels_first(L->nlev); L->l2 = levels_second(L->nlev); }
        FR_AWAIT(k, L->h, F_FIELD, t, 1);
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, L->l1, LEVELS_NONE, 0, NULL, 0));
        FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, L->l2, LEVELS_NONE, 0, NULL, 0));
        FR_CALL(k, r, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
        FR_FINISH(k, RQ(0, r));
    }

    /* cset / csetlv: the record rebuilt, every field under its binder
     * opened at one variable named by this eliminator */
    L->rk = NO_REPL;
    if (L->tag == T_CSETLV) {
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        OBS_CODE(L->b, L->bt, L->b);
        if (L->bt != T_QLV) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->l1, F_HEAD, L->b, 0);
        FR_AWAIT(k, L->b, F_FIELD, t, 2);
        OBS_CODE(L->b, L->bt, L->b);
        if (L->bt != T_QLV) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->l2, F_HEAD, L->b, 0);
        if (L->xt == T_UNIVERSE) { if (L->l1 == LEVEL_NONE) FR_FINISH(k, RQ(3, 0)); L->npay = L->l1; }
        else L->nlev = levels_pack(L->l1, L->l2);
    } else {
        if (L->tag != T_CSET && L->tag != T_CSETB) die("code: %s is no code eliminator", tag_name(L->tag));
        if (L->payload >= L->nf) FR_FINISH(k, RQ(3, 0));
        if ((L->tag == T_CSETB) != (L->xt != T_SYSTEM && schema_slot(L->xt, L->payload) != NO_SLOT)) FR_FINISH(k, RQ(3, 0));
        L->rk = L->payload;
        FR_AWAIT(k, L->fv, F_FIELD, t, 1);              /* the replacement */
    }
    if (L->xt == T_SYSTEM) {
        creq_system_begin(&L->wb, L->nf / 2);
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (L->q == L->rk) {
                OBS_CODE(L->b, L->bt, L->fv);
                if (L->bt != code_of_kind(schema_kind(T_SYSTEM, L->q))) { wordbuf_clear(&L->wb); FR_FINISH(k, RQ(3, 0)); }
                FR_AWAIT(k, r, F_FIELD, L->b, 0);
            } else FR_AWAIT(k, r, F_FIELD, L->x, L->q);
            wordbuf_push(&L->wb, schema_kind(T_SYSTEM, L->q)); wordbuf_push(&L->wb, NO_SLOT); wordbuf_push(&L->wb, r);
        }
        wordbuf_push(&L->wb, 0);
        FR_CALL(k, r, creq_buf(k, &L->wb));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    for (L->q = 0; L->q < L->nf; L->q++) {
        if (L->bs && !L->var && (L->bs == S_DIM || L->q > 0)) {
            /* the binder's variable, bound by the rebuilt record (the
             * record keeps no declaration of it: a term variable is
             * declared at Code, so a program may open a binder whose
             * domain is partial) */
            if (L->bs == S_DIM) { L->var = binder_dim_var(t, 0); L->img = iv_var(L->var); }
            else {
                FR_CALL(k, L->code, mk_tag_sub(k, T_CODE, 0, LEVELS_NONE, 0, NULL, 0));
                L->var = binder_term_var(t, 0, L->code);
                FR_AWAIT(k, L->img, F_REFVAR, L->var, 0);
            }
        }
        if (L->q == L->rk && schema_slot(L->xt, L->q) != NO_SLOT) {
            FR_CALL(k, r, MK_SUB(k, L->bs == S_TERM ? T_QUOTE : T_QIV, 0, LEVELS_NONE, 0, L->img));
            FR_CALL(k, r, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->fv, r));
            OBS_CODE(L->b, L->bt, r);
            if (L->bt != code_of_kind(schema_kind(L->xt, L->q))) FR_FINISH(k, RQ(3, 0));
            FR_AWAIT(k, L->ids[L->q], F_FIELD, L->b, 0);
        } else if (L->q == L->rk) {
            OBS_CODE(L->b, L->bt, L->fv);
            if (L->bt != code_of_kind(schema_kind(L->xt, L->q))) FR_FINISH(k, RQ(3, 0));
            FR_AWAIT(k, L->ids[L->q], F_FIELD, L->b, 0);
        } else if (schema_slot(L->xt, L->q) != NO_SLOT)
            FR_AWAIT(k, L->ids[L->q], F_BINDER, L->x, binder_req(L->bs, schema_slot(L->xt, L->q), L->q, L->img));
        else FR_AWAIT(k, L->ids[L->q], F_FIELD, L->x, L->q);
    }
    FR_CALL(k, r, mk_tag_sub(k, L->xt, L->npay, L->nlev, L->nf, L->ids, L->var));
    FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
    FR_FINISH(k, RQ(0, r));
    FR_END(k);
}

void code_families_init(void) {
    family_define(F_CODE, "code.reduct", code_step, sizeof(CdLoc));
}
