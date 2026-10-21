/* code.c — the records the machine runs, as values of the language.
 *
 * A code is a record former applied to a record: (quote t) holds a term
 * record, (qiv r) an interval record, (qfc φ) a face record, (qlv l) a
 * level; (cnone) is the code an operation gives outside its domain. Nothing
 * else is a representation of syntax: the record a quote holds is the record
 * the machine evaluates. Each code eliminator is one native rule over those
 * records. Its operand fields (schema `opnd`) are evaluated first, all
 * launched together; when an operand is not a code, the eliminator's value
 * is its residual: the eliminator with its operands replaced by their
 * values.
 *
 *   cmatch[f](c, h, d)   the former of c is f: h applied to c's arguments
 *                        (code_arg_kind: fields as codes, a field under a
 *                        binder as the function λa. cinst/cinsti[k](c, a);
 *                        a system as (qfc φ) (quote t) (quote rest); an
 *                        absent optional field as (cnone)); otherwise d
 *   cinst[k](c, a)       field k of c, under a term binder, opened at a
 *   cinsti[k](c, r)      … under a dimension binder, opened at r
 *   cset[k](c, d)        c with field k (under no binder) replaced by d
 *   csetb[k](c, d)       c with field k, under a term binder, replaced by
 *                        d applied to the code of the binder's variable
 *   csetbi[k](c, d)      … under a dimension binder
 *   ceq(a, b, t, f)      t when a and b are one code, otherwise f
 *   cent(a, b, t, f)     t when the face a entails the face b, otherwise f
 *   cfcend[ε](r)         the face (r = ε)
 *   cunfold(c, h, d)     h applied to the code of the body of the defined
 *                        symbol c (pending until its body is supplied); d
 *                        when c is no symbol or an opaque one
 *   clevels(c, h)        h applied to the level codes of c's annotation
 *   csetlv(c, l, m)      c with the annotation l, m
 *   clsucc(l), clmax(l, m)
 *   cop[o](a, b)         ¬a, a∧b, a∨b on interval codes; φ∧ψ, φ∨ψ on face
 *                        codes; ∀a.ψ for the code a of a dimension variable
 *   csyscons(φ, t, s)    the system s with the branch φ ↦ t in front
 *   cvar(c), cvari(c)    the code of the variable of c's term / dimension
 *                        binder (the name the machine opens c's fields at)
 *   csubst(c, v, a)      c with the variable whose code is v replaced by a
 *   ctype(c)             the declared type of the variable or symbol c
 *   cpayload(c)          the payload of c's record, as a level code
 *   cfield(f, k)         the kind of argument k of the former f
 *                        (code_arg_kind), +8 for an operand field
 *   cquote(w)            the code of the term w (w a code)
 *   cstep(c)             the code of the value of the code eliminator coded
 *                        by c under this rule (its residual when an operand
 *                        is not a code)
 *
 * F_CODE(t, 0) is RQ(0, reduct) or RQ(1, residual). */
#include "eval.h"
#include "template.h"
#include "interval.h"
#include "scope.h"

/* the kind of argument k of the former f, the one definition read by
 * cmatch and cfield: 0 none, 1 a term code, 2 an interval code, 3 a face
 * code, 4 a function on term codes (a field under a term binder), 5 a
 * function from interval codes (under a dimension binder) */
enum { CA_NONE = 0, CA_TERM, CA_IV, CA_FC, CA_FUN, CA_FUNI };
static unsigned code_arg_kind(uint64_t f, uint64_t k) {
    if (f == T_SYSTEM) return k == 0 ? CA_FC : k < 3 ? CA_TERM : CA_NONE;
    if (f == 0 || f > T_LAST) return CA_NONE;
    const TagSchema *s = tag_schema((Tag)f);
    if (k >= s->nf) return CA_NONE;
    if (schema_slot((Tag)f, k) != NO_SLOT) return s->bsort == S_TERM ? CA_FUN : CA_FUNI;
    FieldKind fk = schema_kind((Tag)f, k);
    return fk == F_REF ? CA_TERM : fk == F_INTERVAL ? CA_IV : CA_FC;
}
static bool is_code(RefId c) {
    if (ref_is_var(c)) return false;
    Tag t = ref_tag(c);
    return t == T_QUOTE || t == T_QIV || t == T_QFC || t == T_QLV || t == T_CNONE;
}
static Tag code_of_kind(uint64_t kind) { return kind == F_REF ? T_QUOTE : kind == F_INTERVAL ? T_QIV : T_QFC; }
static bool opnd(Tag tag, size_t q) { return tag_schema(tag)->opnd >> q & 1; }

typedef struct {
    Tag tag, xt; uint64_t payload, nf, h, var, img, code, fv, r2, l1, l2, npay, nlev;
    uint64_t f[6], val[6], pl[6], ids[6]; Tag ct[6];
    size_t q, rk; Sort bs; WordBuf wb; bool changed;
} CdLoc;
#define NO_REPL ((size_t)-1)

static void code_step(Cont *k, uint64_t v) {
    CdLoc *L = FR_LOC(k, CdLoc);
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    L->tag = ref_tag(t);
    L->nf = tag_schema(L->tag)->nf;
    FR_AWAIT(k, L->payload, F_HEAD, t, 0);
    /* the operands: launched together, then awaited */
    for (L->q = 0; L->q < L->nf; L->q++) FR_AWAIT(k, L->f[L->q], F_FIELD, t, L->q);
    for (L->q = 0; L->q < L->nf; L->q++) if (opnd(L->tag, L->q)) { family_launch(F_WHNF, L->f[L->q], 0); FR_YIELD(k); }
    for (L->q = 0; L->q < L->nf; L->q++) if (opnd(L->tag, L->q)) FR_AWAIT(k, L->val[L->q], F_WHNF, L->f[L->q], 0);
    for (L->q = 0; L->q < L->nf; L->q++) {
        if (!opnd(L->tag, L->q)) continue;
        if (!is_code(L->val[L->q])) goto stuck;
        L->ct[L->q] = ref_tag(L->val[L->q]);
        if (L->ct[L->q] == T_QLV) FR_AWAIT(k, L->pl[L->q], F_HEAD, L->val[L->q], 0);
        else if (L->ct[L->q] == T_CNONE) L->pl[L->q] = 0;
        else FR_AWAIT(k, L->pl[L->q], F_FIELD, L->val[L->q], 0);
    }

    if (L->tag == T_CEQ) {
        r = L->ct[0] == L->ct[1] && L->pl[0] == L->pl[1];
        FR_FINISH(k, RQ(0, L->f[r ? 2 : 3]));
    }
    if (L->tag == T_CQUOTE) {
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, L->val[0]));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CMATCH) {
        /* the former of the code */
        L->xt = L->ct[0] == T_QIV ? FORMER_IVCODE : L->ct[0] == T_QFC ? FORMER_FCCODE : L->ct[0] == T_QLV ? FORMER_LVCODE
              : L->ct[0] == T_CNONE ? T_CNONE : ref_is_var(L->pl[0]) ? 0 : ref_tag(L->pl[0]);
        if (L->xt == T_SYSTEM && !tnode_nfields(ref_tnode(L->pl[0]))) L->xt = FORMER_SYS0;
        if (L->xt != L->payload) FR_FINISH(k, RQ(0, L->f[2]));
        L->h = L->f[1];
        if (L->xt == T_SYSTEM) {
            /* the first branch and the rest */
            FR_AWAIT(k, r, F_FIELD, L->pl[0], 0);
            FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
            FR_AWAIT(k, r, F_FIELD, L->pl[0], 1);
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
            L->nf = tnode_nfields(ref_tnode(L->pl[0]));
            creq_system_begin(&L->wb, L->nf / 2 - 1);
            for (L->q = 2; L->q < L->nf; L->q += 2) {
                FR_AWAIT(k, L->fv, F_FIELD, L->pl[0], L->q);
                FR_AWAIT(k, r, F_FIELD, L->pl[0], L->q + 1);
                creq_system_branch(&L->wb, L->fv, r);
            }
            wordbuf_push(&L->wb, 0);
            FR_CALL(k, r, creq_buf(k, &L->wb));
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
            FR_FINISH(k, RQ(0, L->h));
        }
        L->nf = L->ct[0] == T_QUOTE && L->xt && L->xt <= T_LAST ? tnode_nfields(ref_tnode(L->pl[0])) : 0;
        for (L->q = 0; code_arg_kind(L->xt, L->q) != CA_NONE; L->q++) {
            if (L->q >= L->nf) FR_CALL(k, L->fv, mk_tag_sub(k, T_CNONE, 0, LEVELS_NONE, 0, NULL, 0));   /* an absent optional field */
            else if (code_arg_kind(L->xt, L->q) >= CA_FUN) {
                /* λ(a). cinst/cinsti[q](c, a), a of the binder's kind of
                 * code, its variable named by this eliminator and the field */
                FR_CALL(k, L->code, mk_tag_sub(k, T_CODE, code_arg_kind(L->xt, L->q) == CA_FUN ? CK_TERM : CK_IV, LEVELS_NONE, 0, NULL, 0));
                L->var = binder_term_var(t, (BinderSlot)L->q, L->code);
                FR_AWAIT(k, r, F_REFVAR, L->var, 0);
                FR_CALL(k, r, MK_SUB(k, code_arg_kind(L->xt, L->q) == CA_FUN ? T_CINST : T_CINSTI, L->q, LEVELS_NONE, 0, L->val[0], r));
                FR_CALL(k, L->fv, MK_SUB(k, T_LAM, 0, LEVELS_NONE, L->var, L->code, r));
            } else {
                FR_AWAIT(k, L->fv, F_FIELD, L->pl[0], L->q);
                FR_CALL(k, L->fv, MK_SUB(k, code_of_kind(schema_kind(L->xt, L->q)), 0, LEVELS_NONE, 0, L->fv));
            }
            FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, L->fv));
        }
        FR_FINISH(k, RQ(0, L->h));
    }
    /* an operation on (cnone) is (cnone) */
    for (L->q = 0; L->q < L->nf; L->q++) if (opnd(L->tag, L->q) && L->ct[L->q] == T_CNONE) goto none;

    if (L->tag == T_CENT) {
        if (L->ct[0] != T_QFC || L->ct[1] != T_QFC) goto none;
        FR_AWAIT(k, r, F_FCENT, L->pl[0], L->pl[1]);
        FR_FINISH(k, RQ(0, L->f[r == 2 ? 2 : 3]));
    }
    if (L->tag == T_CFCEND) {
        if (L->ct[0] != T_QIV) goto none;
        FR_AWAIT(k, r, F_FCEND, L->pl[0], L->payload);
        FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CLSUCC || L->tag == T_CLMAX) {
        if (L->ct[0] != T_QLV || (L->tag == T_CLMAX && L->ct[1] != T_QLV)) goto none;
        if (L->tag == T_CLSUCC) { FR_LSUCC(k, r, L->pl[0]); }
        else { FR_LMAX(k, r, L->pl[0], L->pl[1]); }
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, r, LEVELS_NONE, 0, NULL, 0));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_COP) {
        if (L->payload <= COP_IVOR) {
            if (L->ct[0] != T_QIV || L->ct[1] != T_QIV) goto none;
            if (L->payload == COP_IVNEG) FR_AWAIT(k, r, F_IVNEG, L->pl[0], 0);
            else if (L->payload == COP_IVAND) FR_AWAIT(k, r, F_IVMEET, L->pl[0], L->pl[1]);
            else FR_AWAIT(k, r, F_JOIN, L->pl[0], L->pl[1]);
            FR_CALL(k, r, MK_SUB(k, T_QIV, 0, LEVELS_NONE, 0, r));
            FR_FINISH(k, RQ(0, r));
        }
        if (L->payload == COP_FORALL) {
            /* ∀ over the dimension variable a: its interval is one positive atom */
            size_t n; const uint64_t *w = L->ct[0] == T_QIV ? rget(L->pl[0], &n) : NULL;
            if (!w || n != 2 || w[1] != DNF_SEP || IV_ATOM_NEG(w[0]) || L->ct[1] != T_QFC) goto none;
            FR_AWAIT(k, r, F_FCFORALL, L->pl[1], IV_ATOM_DIM(w[0]));
        } else {
            if (L->ct[0] != T_QFC || L->ct[1] != T_QFC) goto none;
            if (L->payload == COP_FCAND) FR_AWAIT(k, r, F_FCMEET, L->pl[0], L->pl[1]);
            else FR_AWAIT(k, r, F_JOIN, L->pl[0], L->pl[1]);
        }
        FR_CALL(k, r, MK_SUB(k, T_QFC, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CFIELD) {
        if (L->ct[0] != T_QLV || L->ct[1] != T_QLV) goto none;
        r = code_arg_kind(L->pl[0], L->pl[1]);
        if (L->pl[0] >= T_FIRST_CODE_ELIM && L->pl[0] <= T_LAST && L->pl[1] < 8 && opnd((Tag)L->pl[0], L->pl[1])) r += 8;
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, r, LEVELS_NONE, 0, NULL, 0));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CSUBST) {
        /* v: the code of a variable (a term variable, or one positive atom) */
        if (L->ct[0] == T_QLV) goto none;
        if (L->ct[1] == T_QUOTE && L->ct[2] == T_QUOTE && ref_is_var(L->pl[1])) L->r2 = map_single_term(ref_var_id(L->pl[1]), L->pl[2]);
        else if (L->ct[1] == T_QIV && L->ct[2] == T_QIV) {
            size_t n; const uint64_t *w = rget(L->pl[1], &n);
            if (n != 2 || w[1] != DNF_SEP || IV_ATOM_NEG(w[0])) goto none;
            L->r2 = map_single_dim(IV_ATOM_DIM(w[0]), L->pl[2]);
        } else goto none;
        FR_AWAIT(k, r, L->ct[0] == T_QUOTE ? F_TREF : L->ct[0] == T_QIV ? F_TIV : F_TFC, L->pl[0], re_key(L->r2));
        FR_CALL(k, r, MK_SUB(k, L->ct[0], 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CSYSCONS) {
        if (L->ct[0] != T_QFC || L->ct[1] != T_QUOTE || L->ct[2] != T_QUOTE || ref_is_var(L->pl[2]) || ref_tag(L->pl[2]) != T_SYSTEM) goto none;
        L->nf = tnode_nfields(ref_tnode(L->pl[2]));
        creq_system_begin(&L->wb, L->nf / 2 + 1);
        creq_system_branch(&L->wb, L->pl[0], L->pl[1]);
        for (L->q = 0; L->q < L->nf; L->q += 2) {
            FR_AWAIT(k, L->fv, F_FIELD, L->pl[2], L->q);
            FR_AWAIT(k, r, F_FIELD, L->pl[2], L->q + 1);
            creq_system_branch(&L->wb, L->fv, r);
        }
        wordbuf_push(&L->wb, 0);
        FR_CALL(k, r, creq_buf(k, &L->wb));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }

    /* the remaining operations take the code of a term record */
    if (L->ct[0] != T_QUOTE) goto none;

    if (L->tag == T_CUNFOLD) {
        L->fv = 0;
        if (!ref_is_var(L->pl[0]) && ref_tag(L->pl[0]) == T_GLOBAL) {
            FR_AWAIT(k, L->npay, F_HEAD, L->pl[0], 0);
            if (!global_opaque((SymbolId)L->npay)) FR_AWAIT(k, L->fv, F_INPUT, L->npay, 0);   /* the body: an input, pending until supplied */
        }
        if (!L->fv) FR_FINISH(k, RQ(0, L->f[2]));
        FR_AWAIT(k, r, F_UNFOLD, L->pl[0], L->fv);
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_CALL(k, r, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->f[1], r));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CTYPE) {
        if (ref_is_var(L->pl[0])) FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, term_var_type(ref_var_id(L->pl[0]))));
        else {
            if (ref_tag(L->pl[0]) != T_GLOBAL) goto none;
            FR_AWAIT(k, r, F_HEAD, L->pl[0], 0);
            FR_AWAIT(k, r, F_UNFOLD, L->pl[0], global_decl_type((SymbolId)r));
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        }
        FR_FINISH(k, RQ(0, r));
    }

    if (ref_is_var(L->pl[0])) goto none;
    L->xt = ref_tag(L->pl[0]);
    L->nf = tnode_nfields(ref_tnode(L->pl[0]));
    L->bs = L->xt == T_SYSTEM ? 0 : (Sort)tag_schema(L->xt)->bsort;
    FR_AWAIT(k, L->npay, F_HEAD, L->pl[0], 0);
    FR_AWAIT(k, L->nlev, F_HEAD, L->pl[0], 1);

    if (L->tag == T_CSTEP) {
        if (L->xt < T_FIRST_CODE_ELIM) goto none;
        FR_AWAIT(k, r, F_CODE, L->pl[0], 0);
        {   size_t n; const uint64_t *q = rget(r, &n); r = q[1]; }
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CPAYLOAD) {
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, L->npay, LEVELS_NONE, 0, NULL, 0));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CVAR || L->tag == T_CVARI) {
        if (L->bs != (L->tag == T_CVAR ? S_TERM : S_DIM)) goto none;
        if (L->bs == S_DIM) FR_CALL(k, r, MK_SUB(k, T_QIV, 0, LEVELS_NONE, 0, iv_var(binder_dim_var(L->pl[0], 0))));
        else {
            FR_AWAIT(k, L->fv, F_FIELD, L->pl[0], 0);
            FR_AWAIT(k, r, F_REFVAR, binder_term_var(L->pl[0], 0, L->fv), 0);
            FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        }
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CINST || L->tag == T_CINSTI) {
        if (L->payload >= L->nf || schema_slot(L->xt, L->payload) == NO_SLOT || L->bs != (L->tag == T_CINST ? S_TERM : S_DIM)
            || L->ct[1] != (L->tag == T_CINST ? T_QUOTE : T_QIV)) goto none;
        FR_AWAIT(k, r, F_BINDER, L->pl[0], binder_req(L->bs, schema_slot(L->xt, L->payload), L->payload, L->pl[1]));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    if (L->tag == T_CLEVELS) {
        if (L->xt == T_UNIVERSE) { L->l1 = L->npay; L->l2 = LEVEL_NONE; }
        else { L->l1 = levels_first(L->nlev); L->l2 = levels_second(L->nlev); }
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, L->l1, LEVELS_NONE, 0, NULL, 0));
        FR_CALL(k, L->h, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->f[1], r));
        FR_CALL(k, r, mk_tag_sub(k, T_QLV, L->l2, LEVELS_NONE, 0, NULL, 0));
        FR_CALL(k, r, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->h, r));
        FR_FINISH(k, RQ(0, r));
    }

    /* cset / csetb / csetbi / csetlv: the record rebuilt, every field
     * under its binder opened at one variable named by this eliminator */
    L->rk = NO_REPL;
    if (L->tag == T_CSETLV) {
        if (L->ct[1] != T_QLV || L->ct[2] != T_QLV) goto none;
        if (L->xt == T_UNIVERSE) { if (L->pl[1] == LEVEL_NONE) goto none; L->npay = L->pl[1]; }
        else L->nlev = levels_pack(L->pl[1], L->pl[2]);
    } else {
        if (L->tag != T_CSET && L->tag != T_CSETB && L->tag != T_CSETBI) die("code: %s is no code eliminator", tag_name(L->tag));
        if (L->payload >= L->nf) goto none;
        L->rk = L->payload;
        if (L->tag == T_CSET) {
            if ((L->xt != T_SYSTEM && schema_slot(L->xt, L->rk) != NO_SLOT) || L->ct[1] != code_of_kind(schema_kind(L->xt, L->rk))) goto none;
        } else if (L->xt == T_SYSTEM || schema_slot(L->xt, L->rk) == NO_SLOT || L->bs != (L->tag == T_CSETB ? S_TERM : S_DIM)) goto none;
    }
    if (L->xt == T_SYSTEM) {
        creq_system_begin(&L->wb, L->nf / 2);
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (L->q == L->rk) r = L->pl[1];
            else FR_AWAIT(k, r, F_FIELD, L->pl[0], L->q);
            wordbuf_push(&L->wb, schema_kind(T_SYSTEM, L->q)); wordbuf_push(&L->wb, NO_SLOT); wordbuf_push(&L->wb, r);
        }
        wordbuf_push(&L->wb, 0);
        FR_CALL(k, r, creq_buf(k, &L->wb));
        FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
        FR_FINISH(k, RQ(0, r));
    }
    for (L->q = 0; L->q < L->nf; L->q++) {
        if (L->bs && !L->var && (L->bs == S_DIM || L->q > 0)) {
            /* the binder's variable: a term binder's is declared at the
             * (possibly replaced) domain, field 0 */
            if (L->bs == S_DIM) { L->var = binder_dim_var(t, 0); L->img = iv_var(L->var); }
            else {
                L->var = binder_term_var(t, 0, L->ids[0]);
                FR_AWAIT(k, L->img, F_REFVAR, L->var, 0);
            }
        }
        if (L->q == L->rk && L->tag != T_CSET) {
            /* d applied to the code of the variable; its value a term code */
            FR_CALL(k, r, MK_SUB(k, L->bs == S_TERM ? T_QUOTE : T_QIV, 0, LEVELS_NONE, 0, L->img));
            FR_CALL(k, r, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->f[1], r));
            FR_AWAIT(k, r, F_WHNF, r, 0);
            if (ref_is_var(r) || ref_tag(r) != T_QUOTE) goto none;
            FR_AWAIT(k, L->ids[L->q], F_FIELD, r, 0);
        } else if (L->q == L->rk) L->ids[L->q] = L->pl[1];
        else if (schema_slot(L->xt, L->q) != NO_SLOT)
            FR_AWAIT(k, L->ids[L->q], F_BINDER, L->pl[0], binder_req(L->bs, schema_slot(L->xt, L->q), L->q, L->img));
        else FR_AWAIT(k, L->ids[L->q], F_FIELD, L->pl[0], L->q);
    }
    FR_CALL(k, r, mk_tag_sub(k, L->xt, L->npay, L->nlev, L->nf, L->ids, L->var));
    FR_CALL(k, r, MK_SUB(k, T_QUOTE, 0, LEVELS_NONE, 0, r));
    FR_FINISH(k, RQ(0, r));

none:
    FR_CALL(k, r, mk_tag_sub(k, T_CNONE, 0, LEVELS_NONE, 0, NULL, 0));
    FR_FINISH(k, RQ(0, r));
stuck:
    /* an operand that is not a code: the residual, with the operands' values */
    L->changed = false;
    for (L->q = 0; L->q < L->nf; L->q++) {
        L->ids[L->q] = opnd(L->tag, L->q) ? L->val[L->q] : L->f[L->q];
        if (L->ids[L->q] != L->f[L->q]) L->changed = true;
    }
    if (!L->changed) FR_FINISH(k, RQ(1, t));
    FR_CALL(k, r, mk_tag_sub(k, L->tag, L->payload, LEVELS_NONE, L->nf, L->ids, 0));
    FR_FINISH(k, RQ(1, r));
    FR_END(k);
}

/* the input family: an entry no producer publishes; its supplier publishes
 * it (eval_supply). Its one step leaves the entry pending. */
static void input_step(Cont *k, uint64_t v) { (void)k; (void)v; }

void code_families_init(void) {
    family_define(F_CODE, "code.reduct", code_step, sizeof(CdLoc));
    family_define(F_INPUT, "input", input_step, 0);
}
