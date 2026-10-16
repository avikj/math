/* The author's review interface (proof_boundary.h) served by the production
 * proof-use boundary (src/proof.c). The reference implementation shipped with
 * the v11 handoff is kept verbatim in tests/reference/proof_boundary_ref.c;
 * tests/test_proof_parity.c runs both on the same judgments. */
#include "proof_boundary.h"
#include "../src/proof.h"

ProofBoundary proof_boundary(ContextId G, FaceId face, RefId e, RefId T) {
    ProofUse u = proof_use(G, face, e, T);
    ProofBoundary out; memset(&out, 0, sizeof out);
    out.status = (ProofBoundaryStatus)u.status; out.context = G; out.face = face; out.evidence = e; out.type = T;
    out.environment = u.env; out.reason = u.reason;
    words_init(&out.assumptions); words_init(&out.recursive);
    words_append(&out.assumptions, u.assumptions, u.nassumptions);
    words_append(&out.recursive, u.recursive, u.nrecursive);
    return out;
}
void proof_boundary_free(ProofBoundary *r) { words_free(&r->assumptions); words_free(&r->recursive); }
