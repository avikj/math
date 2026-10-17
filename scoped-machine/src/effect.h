/* effect.h — witnessed effects, authority and cuts (EFFECT-AUTHORITY.md).
 *
 * The local realization of the authority boundary inside the machine. Every
 * mathematical payload is an ordinary scoped core reference checked by the
 * existing kernel: an effect schema is (Γ, κ, In, Out, R) with
 * R : In → Out → U; a proposal supplies the edge witness p, and its source
 * s : In and target t : Out are built by the machine from the expected input
 * heads and the proposed output states / port payloads, never taken on
 * trust. Two judgments stay distinct:
 *   mathematical admission — Γ;κ ⊢ s : In, t : Out, p : R s t, each through
 *     the framed proof-use audit (CORE or ASSUMED; ASSUMED keeps its opaque
 *     assumptions in the occurrence's premises; PENDING / UNRESOLVED leaves
 *     the proposal pending, INVALID settles it);
 *   operational acceptance — the RESERVING → COMMITTED transition of one
 *     commit descriptor after every input cell is reserved by it, in the
 *     fixed total order of cell identities.
 * The records are descriptors and jobs of the existing machine: every step
 * (each preparation phase and audit unit, each reservation, the commit, each
 * finalization, each receipt delivery and emission) is one job of the
 * evaluator's scheduler (eval_job), so holds, budgets and worker pools apply.
 * No numeral, Boolean, account or payment primitive is introduced: the cash
 * instance of the acceptance witness is a schema over Church numerals. */
#ifndef CUBICAL_EFFECT_H
#define CUBICAL_EFFECT_H
#include "check.h"
#include "proof.h"
#include "xcount.h"

typedef struct EffSchema EffSchema;
typedef struct EffAuthority EffAuthority;
typedef struct EffHead EffHead;
typedef struct EffPort EffPort;
typedef struct EffCap EffCap;
typedef struct EffOcc EffOcc;          /* an occurrence; once accepted, its pointer is the receipt's identity */
typedef struct EffProposal EffProposal;
typedef struct EffCommit EffCommit;    /* the shared prepare/commit descriptor of one request identity */

typedef enum { EO_PENDING = 0, EO_ACCEPTED, EO_CONFLICT, EO_INVALID, EO_REQUEST_CONFLICT } EffOutcomeKind;
typedef struct { EffOutcomeKind kind; const EffOcc *receipt; const EffOcc *holder; const char *why; } EffOutcome;   /* holder: for a conflict, the occurrence that consumed the input */
typedef void (*EffDeliver)(void *ctx, EffOutcome o);

/* scheduler tags of the effect jobs (EvalTaskInfo.tag) */
enum { EFF_TAG_PREPARE = 0x4E00, EFF_TAG_AUDIT, EFF_TAG_RESERVE, EFF_TAG_COMMIT, EFF_TAG_FINALIZE, EFF_TAG_DELIVER, EFF_TAG_EMIT };
/* how an input port's consumption is authorized */
enum { EFF_PORT_RECIPIENT = 1, EFF_PORT_REFUND = 2 };

void effect_init(void);
void effect_free(void);                 /* closed-session teardown (after eval_free: no effect job runs any more) */

EffSchema *eff_schema(const char *name, ContextId G, FaceId kappa, RefId In, RefId Out, RefId R, int port_role);
/* genesis: an authority with its initial head (state : type in the schema context) and an owner capability */
EffAuthority *eff_genesis(const char *name, ContextId G, FaceId kappa, RefId state, RefId type, EffCap **owner);
const char *eff_authority_name(const EffAuthority *a);

EffProposal *eff_proposal(EffSchema *s, uint64_t ns, uint64_t request);
void eff_in_head(EffProposal *P, EffAuthority *a, const EffHead *expected);
void eff_in_port(EffProposal *P, EffPort *m);
void eff_out_head(EffProposal *P, EffAuthority *a, RefId state);
void eff_out_port(EffProposal *P, RefId payload, EffAuthority *recipient, EffAuthority *refund_to);
void eff_witness(EffProposal *P, RefId p);
void eff_cap(EffProposal *P, EffCap *c);
void eff_proposal_free(EffProposal *P);              /* a recipe that was not requested */
EffProposal *eff_proposal_reindex(const EffProposal *P, MapId sigma, uint64_t request);   /* the recipe at the instantiated boundary: no request, no acceptance */
/* EFFECT_REQUEST: install or join the request's descriptor; k receives its outcome (once, by a counted delivery job) */
EffCommit *eff_request(EffProposal *P, EffDeliver k, void *ctx);
EffOutcomeKind eff_commit_state(const EffCommit *d);  /* PENDING while preparing / reserving */
bool eff_commit_unresolved(const EffCommit *d);       /* a required proof is pending (the descriptor stays pending, its clients attached) */
size_t eff_retry(void);                              /* a new attempt: re-run the audits of every pending descriptor; returns how many */

/* readings of the current cut (a reserved cell is resolved through its descriptor's state) */
const EffHead *eff_head(EffAuthority *a);
RefId eff_head_state(const EffHead *h);
const EffOcc *eff_head_producer(const EffHead *h);    /* NULL: genesis */
bool eff_port_open(EffPort *m);
/* a consistent cut: the logical head of every authority and every open port, read between two equal even
 * values of the commit sequence (no commit transition intervenes) */
typedef struct { size_t nheads; EffAuthority **auth; const EffHead **head; size_t nopen; EffPort **open; } EffCut;
bool eff_cut_snapshot(EffCut *out);
void eff_cut_free(EffCut *c);
size_t eff_ports(EffPort ***out);                     /* every port of an accepted occurrence (caller frees *out) */
size_t eff_authorities(EffAuthority ***out);
RefId eff_port_payload(const EffPort *m);
EffAuthority *eff_port_recipient(const EffPort *m);
const EffOcc *eff_port_issuer(const EffPort *m);
const EffOcc *eff_port_consumer(EffPort *m);          /* the accepted occurrence that consumed it, or NULL */

/* receipts: an accepted occurrence */
uint64_t eff_occ_id(const EffOcc *e);
bool eff_occ_accepted(const EffOcc *e);
const char *eff_occ_schema(const EffOcc *e);
size_t eff_occ_nports(const EffOcc *e);
EffPort *eff_occ_port(const EffOcc *e, size_t slot);
enum { EFF_FIELD_WITNESS = 1, EFF_FIELD_SOURCE, EFF_FIELD_TARGET, EFF_FIELD_EDGE_TYPE };
RefId eff_receipt_observe(const EffOcc *e, int field);   /* RECEIPT_OBSERVE: a field of an accepted occurrence (no acceptance is rerun) */
size_t eff_occ_inputs(const EffOcc *e, const EffOcc **producers, size_t max);   /* causality: the occurrences that produced the consumed inputs (NULL: genesis) */
size_t eff_occ_assumptions(const EffOcc *e, const uint64_t **syms);   /* admitted premises (opaque symbols an ASSUMED audit reached) */
uint64_t eff_occ_env(const EffOcc *e);                                 /* the environment snapshot preparation pinned */
typedef struct { XSnap prepare_steps, audit_units, reservations, waits, commit, finalizes, deliveries, emits; } EffOccWork;
EffOccWork eff_occ_work(const EffOcc *e);
void eff_unattributed(XSnap *prep, XSnap *audit);   /* preparation work of descriptors without an occurrence record (invalid or pending) */
size_t eff_pending_emissions(void);                 /* committed outputs not yet emitted (obligations a durable boundary would retain) */
/* ReceiptView(E, σ, η): a transported description of the same accepted
 * occurrence; η is checked: the same port occurrence and recipient, and the
 * payload's transport reindex(payload, σ) equal to the claimed payload and
 * preserving the resource (the payload is invariant under σ) */
typedef struct { const EffOcc *occ; MapId sigma; size_t slot; RefId payload; EffAuthority *recipient; } EffView;
bool eff_receipt_view(const EffOcc *e, MapId sigma, size_t slot, RefId claimed_payload, EffAuthority *claimed_recipient, EffView *out, const char **why);
bool eff_view_reindex(const EffView *v, MapId tau, EffView *out, const char **why);

/* emission: the outbox of each authority receives the ports addressed to it (descriptions, by port identity) */
size_t eff_outbox(EffAuthority *a, EffPort ***out);   /* emitted ports addressed to a, in emission order (caller frees *out) */

/* the accepted history and the event ledger (exact) */
size_t eff_history(const EffOcc ***out);               /* accepted occurrences in commit order (caller frees *out) */
size_t eff_occurrences(const EffOcc ***out);           /* every prepared occurrence record, accepted or not (caller frees *out) */
typedef struct { size_t requests, joins, request_conflicts, prepares, prepare_steps, audits, audit_units, invalid, unresolved, reservations, waits, helps, commits, aborts, finalizes, deliveries, deliveries_unattributed, emits; } EffEvents;
EffEvents eff_events(void);                            /* checked word projections of the exact counts */
#endif
