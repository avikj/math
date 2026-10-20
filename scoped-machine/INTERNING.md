# Canonical record construction under the one protocol

Review 5886af7 finding 3: two equal 1000-word records inserted serially cost 254 advances,
alternated 377 — both contenders reserved and copied before one lost publication. The id was
right; the counted work depended on the schedule. This note fixes the law the interner must obey,
lists every overlap of the real transitions, and shows the equal-weight join for each. The
implementation follows it exactly (src/intern.c, src/eval.c `intern`, `intern.flatten`).

## 1. The law

For a fixed demand (multiset of record constructions) the counted work W must not depend on the
schedule, and every counted step must be bounded: Instr ≤ c·W + d.

W counts jobs (steps). A job of the interner advances at most B units; each unit is bounded work.
So two things must be schedule-independent: the sequence of units each request performs, and the
places where a request suspends (a suspension ends a step; its resumption is a job).

## 2. Why per-word units over a shared mutable structure cannot satisfy it

Any structure in which the cost of locating record K depends on which *other* records are present
makes W schedule-dependent, because which other records are present when K is located is the
schedule. Three candidate repairs fail on a concrete join:

- Compressed trie, leaves pushed down by later splits: find(K) before vs after insert(J) with
  LCP(J,K) = 20 nibbles costs 1 vs 21 levels.
- Leaves fixed where created (records stay at their creation depth): insert/insert joins are equal
  weight (ultrametric argument: with a = maxLCP(A,S), b = maxLCP(B,S), l = LCP(A,B), the two
  smallest of a,b,l are equal, so a + max(b,l) = b + max(a,l), and the comparison term
  [a < l]·cmp(A,B) = [b < l]·cmp(A,B)), but the two orders leave different states and find(K)
  cost depends on the set created before K; with find multiplicities f_A ≠ f_B the totals differ
  by (f_A − f_B)·cmp(A,B).
- Copy-then-publish (no claim): both equal contenders copy; the loser's copy is wasted. This is
  the reported trace.

And ownership with a claim (R state) plus waiting, over a per-word structure, makes the *places of
suspension* schedule-dependent: whether K meets an in-progress leaf (and must wait) depends on
timing, and a lost edge CAS can make K meet a second leaf.

## 3. The construction

Split canonical construction into two layers with different laws.

**Small records** (n ≤ SMALL_MAX = 16 words). One small intern is one *unit*: descent of the
compressed 16-ary trie over the stream (hash, n, w0..wn−1), comparison with the leaf met, and on
absence reservation, copy and publication by CAS. All of it is bounded by a constant: the stream
is at most 18 words (≤ 288 nibbles), the comparison and copy at most 16 words. A unit never
suspends.

**Large records** (n > 16) are identified by a canonical tree of small records in the table's
auxiliary tree table:

- leaves: [LEAF, w_{15i} .. w_{15i+14}] (the last one shorter), in order;
- inner nodes: [NODE, c_0 .. c_{k−1}], k ≤ 15, built online: when a level holds 15 ids they are
  interned as one node one level up; at the end the partial levels are folded bottom-up, each
  carrying its node into the next level, until a level holds the only id left;
- root: [ROOT, n, top].

Every tree record is a small record, so every tree intern is one unit. The tree depends only on
(n, words): its unit count is a function of n alone (⌈n/15⌉ leaves, the carries and folds of a
fixed counter, one root). The tree root T is the record's content identity, exact (every word is
compared in the small interns; hash equality is never equality).

The **flat record** — the contiguous words that interner_get returns, §9.1 — is the value of the
pure family `intern.flatten` keyed by (table, T). Its one producer walks the tree one leaf per step
copying ≤ 15 words, reserves the record's id and storage, publishes the record, and finishes with
the id. Every requester requests the key: U launches the producer, R waits, D is a ready hit —
the protocol's own request/publication law, with one delivery per request.

## 4. Overlap cases of the real transitions, and their joins

Units and suspensions of one request for record K, length n:

| request | units | suspensions |
|---|---|---|
| n ≤ 16 | 1 small intern | 0 |
| n > 16 | tree(n) small interns | 1 (the flatten request) |

and one producer run per distinct large content per machine generation: leaves(n) steps plus the
start and finish steps.

Overlaps within one small intern (one unit, never split across steps):

1. *Discovery* — two contenders descend the same path: reads only; each unit unchanged.
2. *Reservation* — both find the same empty slot or separating leaf, both reserve an id and up to
   16 words, both copy (≤ 16 words): the loser's CAS fails, it re-reads the slot and compares (≤ 16
   words). Bounded inside the unit; the unit count is 1 for each contender in either order. The
   loser's id and words stay unused (ids are names, not work).
3. *Comparison* — equal content: the later contender compares with the published leaf. Different
   content, same separating slot: the later contender builds its split chain privately (≤ 288
   levels, bounded) and CASes; if the slot changed it continues below it. A slot changes only
   empty → leaf → inner node, so retries are monotone in depth and bounded by the stream length
   (≤ 18 words): each unit's work is bounded by a constant independent of the number of
   workers, so Instr ≤ c·W + d.
4. *Copy* — private to the reserving contender until its CAS.
5. *Publication* — one CAS per contender; the winner's leaf is complete (record words and hash
   stored before the CAS, released by it).

Join: two small interns of any contents commute with weight 1 + 1, and the resulting sets of
published records are equal (ids aside). Hence any interleaving of small interns has weight equal
to their number.

Overlaps of large requests:

6. Two requests of equal content build the same tree: each performs tree(n) small interns
   (identical unit sequences, overlaps 1–5 inside each unit), then each requests the same flatten
   key. The protocol gives one producer, one delivery per request: the requester whose request
   finds U is not distinguished in work from one that finds R or D (each is delivered once, by one
   job). Weight in both orders: 2·tree(n) + 2 deliveries + one producer run.
7. Two requests of different large contents sharing a prefix share leaf and node records (overlap
   cases 1–5 per shared record) and request different flatten keys: weights add.
8. A large request and a small one never share a record (tags and lengths differ): weights add.
9. Retries: inside a unit only (case 3). There is no retry across steps: a request never re-does a
   unit, never re-requests a key.

The repeated request in a later machine generation (eval_reset with the tables kept) launches a
fresh producer, which finds the flat id already published and finishes in one step; W across
generations is not compared (the schedule tests use a fresh machine per run).

## 5. Synchronous construction

Inside a counted step only small records may be interned or found synchronously (one bounded
unit). A large record inside a step is a stepped subroutine (`intern_sub`), which awaits the flatten
key. Outside jobs (roots, tests, the machine before the evaluator exists) a large record builds its
tree inline and obtains the flat record through the root-driving call of the flatten key, or —
with no evaluator — by the owner of an inline claim (a CAS on the root's flat cell; others spin on
an owner that never suspends).

The `created` result of a large record is the creation of its tree root: exactly one request
creates it.
