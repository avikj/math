/* judge.h — checking and conversion as frame families (judge.c). */
#ifndef CUBICAL_JUDGE_H
#define CUBICAL_JUDGE_H

#include "eval.h"

typedef enum { JK_INFER, JK_CHECK, JK_LEVEL, JK_CONVT, JK_CONVt, JK_MAP, JK_CTX, JK_NODE, JK_DECL, JK_BODY, JK_STRUCT, JK_SCOPE, JK_CLAUSES } JudgeKind;
/* request records (each family's key operand a):
 *   INFER [C, t, P]   CHECK [C, t, A, P]   LEVEL [C, A, P]
 *   CONVT [C, A, B, P]   CONVt [C, t, u, A, P]   MAP [D, ψ, σ, Γ, χ, P]
 *   CTX [G, a, P]   SCOPE [G, χ, t]   NODE [Q, P]   DECL / BODY [s, P]   STRUCT [kind, x, 0]
 * G, D, Γ judgment contexts; C a clause (or face); P a pin set; a local
 * judgment reads its variables' own types and is keyed with C projected
 * onto its subjects' support. CLAUSES takes the face itself as its operand. */
Family judge_family(JudgeKind kind);
uint64_t judge_request(size_t n, const uint64_t *w);
/* results [code, reason, a, b, c]: code 1 valid/equal, 2 invalid/unequal, 3 unresolved */
uint64_t judge_res(uint64_t code, const char *why, uint64_t a, uint64_t b, uint64_t c);
uint64_t jr_code(uint64_t v); const char *jr_why(uint64_t v);
uint64_t jr_a(uint64_t v); uint64_t jr_b(uint64_t v); uint64_t jr_c(uint64_t v);
/* judgment contexts */
uint64_t jc_empty(void);
uint64_t jc_ext(uint64_t G, Sort sort, uint64_t id);
uint64_t jc_parent(uint64_t G);
bool jc_is_empty(uint64_t G);
void jc_decl(uint64_t G, Sort *sort, uint64_t *id);
bool jc_term(uint64_t G, TermVarId x);
bool jc_dim(uint64_t G, DimVarId j);
void judge_families_init(void);

#endif
