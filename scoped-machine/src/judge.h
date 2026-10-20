/* judge.h — checking and conversion as frame families (judge.c). */
#ifndef CUBICAL_JUDGE_H
#define CUBICAL_JUDGE_H

#include "eval.h"

/* request records (each judgment family's key operand a, families.h):
 *   INFER [C, t]   CHECK [C, t, A]   LEVEL [C, A]   CONVT [C, A, B]
 *   CONVt [C, t, u, A]   MAP [D, ψ, σ, Γ, χ]   CTX [G, a]   SCOPE [G, χ, t]
 *   NODE [Q]   DECL [s]   BODY [revision]   STRUCT [kind, x, 0]
 * G, D, Γ judgment contexts; C a clause (or face); a local judgment reads
 * its variables' own types and is keyed with C projected onto its subjects'
 * support. EVERY [φ, f, args…] / JOINT [φ, f, args…] judge f at
 * [c, args…] for every clause c of the face φ. Judgments that observe are
 * relative families (eval.h): no view in their keys. */
uint64_t judge_request(size_t n, const uint64_t *w);
/* results [code, reason, a, b, c]: code 1 valid/equal, 2 invalid/unequal, 3 unresolved */
uint64_t judge_res(uint64_t code, const char *why, uint64_t a, uint64_t b, uint64_t c);
uint64_t jr_code(uint64_t v); const char *jr_why(uint64_t v);
uint64_t jr_a(uint64_t v); uint64_t jr_b(uint64_t v); uint64_t jr_c(uint64_t v);
/* judgment contexts */
uint64_t jc_empty(void);
uint64_t jc_parent(uint64_t G);
bool jc_is_empty(uint64_t G);
void jc_decl(uint64_t G, Sort *sort, uint64_t *id);
void judge_families_init(void);

#endif
