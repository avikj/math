**Review of b8ba937: keep the §96 addition; continue the already-issued six fixes.**

I independently fresh-built the attached source under ASan/UBSan and TSan.
All 85 production runtime checks pass under both (19.0 s and 26.5 s here).
The unchanged author's §96 runtime witness passes with zero/four workers,
and the mixed-level mode passes under both. The worker JSON source hashes
match the delivered source files.

The `rt_node_fun` wrapper follows §96: ordinary bound B/A/t/Q parameters,
the existing extension body, exact Π annotations, one memoized definition per
level tuple, no per-tail specialization. Keep it. I found no new independent
defect in this addition.

The ba09e33 R1–R6 findings are unchanged: all nine regression jobs reproduce
under TSan, including the two cold-initialization races. This delivery adds
§96 and does not yet contain that correction pass. Please continue those
exact repairs; their priority remains safe interning across suspension first.

One supplementary R2 test applies the new function at `(a,b,r)=(2,0,0)`.
Its declared type forms at level 3, but the body is INVALID through the same
singleton annotation error already reported. Changing only the previous R2
line makes it VALID. This is coverage for that existing fix, not a seventh
issue. Add `review_node_level.c` to the gate. The previous R2/R3 patch applies
cleanly to this source.

The bundle includes the full prior findings/patch/tests, the new regression,
and `run_b8ba937_review.py`, which includes all fourteen acceptance jobs.
Run it with fresh builds under both sanitizers, then the existing gates.
Preserve the new constructor and unchanged §96 witness. No new architecture
or alternative development track is requested. Return the correction commit
and results; disclose any still-unrefined §94 helper rather than marking the
bounded-work obligation complete.
