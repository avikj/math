/* code.c — the records the machine runs, as values of the language.
 *
 * A code is a record former applied to a record: (quote t) holds a term
 * record, (qiv r) an interval record, (qfc φ) a face record. Nothing else
 * is a representation of syntax: the record a quote holds is the record the
 * machine evaluates. Each code eliminator is one native rule over those
 * records; its value is a reduct term the evaluator then observes.
 *
 *   cmatch[tag](c, h, d)  the former of c is `tag` (0: a variable; T_QIV,
 *                         T_QFC: an interval or face code): h applied to
 *                         c's fields as codes, a field under a binder as the
 *                         function λ(a:Code). cinst[k](c, a); otherwise d
 *   cinst[k](c, a)        the field k of c opened at the term or interval a
 *   ceq(a, b, t, f)       t when a and b are one record, otherwise f
 *   cent(a, b, t, f)      t when the face a entails the face b, otherwise f
 *   cfcend[ε](r)          the face (r = ε)
 *   cunfold(c, h, d)      h applied to the code of the body of the defined
 *                         symbol c; d when c is no symbol with a body
 *
 * F_CODE(t, χ) is the reduct of the code eliminator t under χ, as the
 * record RQ(kind, word): kind 0 the reduct `word`, 1 neutral (the operand
 * is no code introduction), 2 the operand's observation `word` (no
 * observation or invalid), 3 an operand of the wrong kind. */
#include "eval.h"
#include "template.h"

typedef struct {
    Tag tag, ct, bt, xt; uint64_t payload, c, x, b, y, res, h, code, var, fv, r; size_t nf, q;
} CdLoc;
#define RES(id) res_get(id)

static void code_step(Cont *k, uint64_t v) {
    CdLoc *L = FR_LOC(k, CdLoc);
    RefId t = k->w[0]; FaceId chi = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    L->tag = ref_tag(t);
    FR_AWAIT(k, L->payload, F_HEAD, t, 0);
    FR_AWAIT(k, L->c, F_FIELD, t, 0);
    FR_AWAIT(k, L->res, F_OBS, L->c, observe_key(chi, 0));
    if (RES(L->res).cls == R_NO_OBSERVATION || RES(L->res).cls == R_INVALID) FR_FINISH(k, RQ(2, L->res));
    if (RES(L->res).cls != R_INTRODUCTION) FR_FINISH(k, RQ(1, 0));
    L->c = RES(L->res).ref; L->ct = ref_tag(L->c);
    if (L->ct != T_QUOTE && L->ct != T_QIV && L->ct != T_QFC) FR_FINISH(k, RQ(3, 0));
    FR_AWAIT(k, L->x, F_FIELD, L->c, 0);

    if (L->tag == T_CEQ || L->tag == T_CENT) {
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        FR_AWAIT(k, L->res, F_OBS, L->b, observe_key(chi, 0));
        if (RES(L->res).cls == R_NO_OBSERVATION || RES(L->res).cls == R_INVALID) FR_FINISH(k, RQ(2, L->res));
        if (RES(L->res).cls != R_INTRODUCTION) FR_FINISH(k, RQ(1, 0));
        L->b = RES(L->res).ref; L->bt = ref_tag(L->b);
        if (L->bt != T_QUOTE && L->bt != T_QIV && L->bt != T_QFC) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->y, F_FIELD, L->b, 0);
        if (L->tag == T_CEQ) r = L->ct == L->bt && L->x == L->y;
        else {
            if (L->ct != T_QFC || L->bt != T_QFC) FR_FINISH(k, RQ(3, 0));
            FR_AWAIT(k, r, F_FCENT, L->x, L->y);
            r = r == 2;
        }
        FR_AWAIT(k, r, F_FIELD, t, r ? 2 : 3);
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CFCEND) {
        if (L->ct != T_QIV) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, r, F_FCEND, L->x, L->payload);
        FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CUNFOLD) {
        if (L->ct != T_QUOTE) FR_FINISH(k, RQ(3, 0));
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

    if (L->tag == T_CINST) {
        if (L->ct != T_QUOTE || ref_is_var(L->x)) FR_FINISH(k, RQ(3, 0));
        L->xt = ref_tag(L->x);
        if (L->payload >= tnode_nfields(ref_tnode(L->x)) || schema_slot(L->xt, L->payload) == NO_SLOT) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->b, F_FIELD, t, 1);
        FR_AWAIT(k, L->res, F_OBS, L->b, observe_key(chi, 0));
        if (RES(L->res).cls == R_NO_OBSERVATION || RES(L->res).cls == R_INVALID) FR_FINISH(k, RQ(2, L->res));
        if (RES(L->res).cls != R_INTRODUCTION) FR_FINISH(k, RQ(1, 0));
        L->b = RES(L->res).ref; L->bt = ref_tag(L->b);
        if (L->bt != (tag_schema(L->xt)->bsort == S_TERM ? T_QUOTE : T_QIV)) FR_FINISH(k, RQ(3, 0));
        FR_AWAIT(k, L->y, F_FIELD, L->b, 0);
        FR_AWAIT(k, r, F_BINDER, L->x, binder_req(tag_schema(L->xt)->bsort, schema_slot(L->xt, L->payload), L->payload, L->y));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    if (L->tag == T_CMATCH) {
        L->xt = L->ct == T_QUOTE ? (ref_is_var(L->x) ? 0 : ref_tag(L->x)) : L->ct;
        if (L->xt != L->payload) { FR_AWAIT(k, r, F_FIELD, t, 2); FR_FINISH(k, RQ(0, r)); }
        FR_AWAIT(k, L->h, F_FIELD, t, 1);
        if (L->ct != T_QUOTE || L->xt == 0) FR_FINISH(k, RQ(0, L->h));
        FR_CALL(k, L->code, mk_tag_sub(k, T_CODE, 0, LEVELS_NONE, 0, NULL, 0));
        L->nf = tnode_nfields(ref_tnode(L->x));
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (schema_slot(L->xt, L->q) != NO_SLOT) {
                /* a field under a binder: λ(a:Code). cinst[q](c, a), its
                 * variable named by this eliminator and the field */
                L->var = binder_term_var(t, (BinderSlot)L->q, L->code);
                FR_AWAIT(k, r, F_REFVAR, L->var, 0);
                FR_CALL(k, r, MK_SUB(k, T_CINST, L->q, LEVELS_NONE, 0, L->c, r));
                FR_CALL(k, L->fv, MK_SUB(k, T_LAM, 0, LEVELS_NONE, L->var, L->code, r));
            } else {
                FR_AWAIT(k, L->fv, F_FIELD, L->x, L->q);
                r = schema_kind(L->xt, L->q);
                FR_CALL(k, L->fv, MK_SUB(k, r == F_REF ? T_QUOTE : r == F_INTERVAL ? T_QIV : T_QFC, 0, LEVELS_NONE, 0, L->fv));
            }
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, L->fv));
        }
        FR_FINISH(k, RQ(0, L->h));
    }
    die("code: %s is no code eliminator", tag_name(L->tag));
    FR_END(k);
}

void code_families_init(void) {
    family_define(F_CODE, "code.reduct", code_step, sizeof(CdLoc));
}
