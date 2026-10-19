/* effect.h — witnessed effects, authority and ports (EFFECT-AUTHORITY §§1–10).
 *
 * Records are interned immutable records; their payloads are core
 * references checked by the existing kernel. The one mutable state is the
 * cell: an authority's head cell or a port's consumption cell holds
 *   AVAILABLE(head | port)  |  RESERVED(descriptor, slot)  |  CONSUMED(occurrence)
 * and a RESERVED cell is read through its descriptor's state word.
 *
 *   schema      [SCHEMA, S, level, R]          R : S → … → S → U, one argument per state
 *   authority   [AUTHORITY, schema, nonce]
 *   head        [HEAD, authority, occurrence, state, predecessor]       genesis: occurrence 0
 *   port        [PORT, occurrence, slot, payload, recipient authority]
 *   capability  [CAP, authority, nonce]        valid when its authority issued it
 *   proposal    [PROPOSAL, schema, nin, input*, nout, (is_port, authority, value)*,
 *                witness, witness type, ncap, cap*]
 *               inputs are heads or ports (semantic order: R's argument order);
 *               the witness type is R applied to the input states, then the outputs
 *   occurrence  [OCCURRENCE, request id, proposal]
 *
 * EFFECT(rid, P) is one producer per (rid, P): repeated identical requests
 * join it and receive one receipt; a request id claimed by another proposal
 * is a request conflict. PREPARE(P) is a pure keyed family (states, levels,
 * witness, proof use, capabilities). Reservation is one cell per step in the
 * fixed total cell order; the acceptance is one CAS of the descriptor state.
 */
#ifndef CUBICAL_EFFECT_H
#define CUBICAL_EFFECT_H

#include "eval.h"

typedef enum { OUT_ACCEPTED = 1, OUT_CONFLICT, OUT_REQUEST_CONFLICT, OUT_INVALID, OUT_UNRESOLVED } Outcome;
typedef struct { int is_port; uint64_t authority; RefId value; } EffOut;

uint64_t effect_schema(RefId S, uint64_t level, RefId R);
/* a new authority whose head cell holds its genesis head at state s0; *cap
 * receives the owner capability it issues */
uint64_t effect_authority(uint64_t schema, RefId s0, uint64_t nonce, uint64_t *cap);
uint64_t effect_capability_unissued(uint64_t authority, uint64_t nonce);   /* a record no authority issued */
uint64_t effect_proposal(uint64_t schema, size_t nin, const uint64_t *inputs, size_t nout, const EffOut *outs,
                         RefId witness, size_t ncap, const uint64_t *caps);
/* the outcome record of request (rid, P): [OUT_ACCEPTED, occurrence] |
 * [OUT_CONFLICT, cell] | [OUT_REQUEST_CONFLICT] | [OUT_INVALID, reason] | [OUT_UNRESOLVED] */
uint64_t effect_request(uint64_t rid, uint64_t proposal, WhnfStatus *status);
Family effect_family(void);                                   /* "effect.request": keyed (rid, P) */
Outcome outcome_kind(uint64_t out);
uint64_t outcome_occurrence(uint64_t out);
const char *outcome_reason(uint64_t out);

/* the current logical cut */
uint64_t effect_head(uint64_t authority);                     /* the authority's current head */
RefId head_state(uint64_t head);
uint64_t head_occurrence(uint64_t head);
uint64_t head_authority(uint64_t head);
uint64_t effect_port(uint64_t occurrence, size_t slot);      /* the port record of an accepted output */
int port_status(uint64_t port, uint64_t *consumer);           /* 0 absent, 1 available, 2 consumed (consumer = occurrence) */
RefId port_payload(uint64_t port);
size_t effect_open_ports(uint64_t *out, size_t max);         /* unconsumed ports on the current cut */

/* receipts */
bool receipt_accepted(uint64_t occurrence);
uint64_t receipt_proposal(uint64_t occurrence);
uint64_t receipt_view(uint64_t occurrence, MapId sigma);     /* 0: rejected (σ moves its anchored boundary) */
uint64_t receipt_view_occurrence(uint64_t view);

/* Church naturals read exactly (host natural of the normal form) */
bool church_value(RefId n, uint64_t *out);

void effect_families_init(void);
void effect_free(void);

#endif
