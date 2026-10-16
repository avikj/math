**Review of v14 / 4d51993 — R1–R5 accepted; the original R6 drain defect is closed.**

I reviewed this as the response to the ba09e33 six-finding review, not as a
response to the later b8ba937 follow-up. Fresh independent builds pass all
fourteen jobs under ASan/UBSan and TSan: your original twelve, the later
node_(2,0,0) test, and the production runtime's 85 checks. The later node
case is already fixed by R2; it needs no extra constructor change.

Keep the delivered interning transaction, universe/residual corrections,
fixed ap/J/reuse templates and lifecycle changes. The original table-drain
reproduction passes too. The full bounded-step contract remains open exactly
as you disclosed.

One concrete piece remains inside that same R6 work: INTERN's reservation
phase zero-fills the entire payload in one unit. My new probe preallocates
capacity, so it isolates the loop from allocator/growth cost: n=64 writes 64
payload words, n=4096 writes 4096, each with budget/handle-units=1.

The attached `reservation.patch` already fixes this locally: reserve the
exclusive extent by advancing the logical end, write the header, and let the
existing COPY phase initialize each private payload word before publication.
The new probe then writes zero payload words during reservation and completes
to the correct canonical record. The patch passes interleave, same-key,
growth, drain and reservation under both sanitizers. It preserves your R1
repair. Please apply it and add the probe to the gates.

Then continue the already-assigned §94 bounded-step refinement of collision
probes, buffer growth/copying and kernel/audit work; include PREPARE's remaining
bulk buffer/sort paths. Do not call the whole refinement complete from passing
the old drain case, and do not treat the accepted R1–R5 repairs as still open.
No new calculus, planner or runtime is requested.

`run_v14_review.py` consolidates the fifteen acceptance jobs. The full report,
patch, source and independent results are in the bundle. Return the integration
commit and results, retaining an exact account of any §94 work still unfinished.
