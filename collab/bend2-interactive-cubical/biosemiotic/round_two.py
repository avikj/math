#!/usr/bin/env python3
"""Round two of instruments, each licensed by a checked term read in the corpus digests.

  §G  OBSERVABILITY QUOTIENT (automata/ObservabilityQuotient, MyhillNerodeMinimalMachine,
      ProductiveObservabilityBridge): the safe quotient of a state space is ForeverEq =
      ⋂ₙ ker(P Tⁿ), not ker P.  On the empirical whale machine (states = metre × tempo-bin,
      transitions = the observed successor support), bisimulation refinement with the
      METRE as the readout computes the coarsest future-preserving quotient.  Measured:
      how many (metre, tempo) states are identified by their futures — i.e. whether the
      tempo fibre is ever separated by what comes next.
  §H  REVERSAL (theorems/primes/pair_field/ReversalInvariant): list reversal is the ℤ/2 involution; a reading is
      achromatic (blind) or chromatic (sighted) to it; the fixed locus is the palindromes.
      Measured on codas: which readings are reversal-blind, and the repertoire's own
      arrow of time — a metre against its reversal (GGLL vs LLGG).
  §I  PRASNA (residue/Prasna: run-is-answers; silence-is-determinism): the run of an
      interaction is its answer stream.  Read whale B's next coda as the reaction to the
      environment's answer (A's last coda) versus B's own previous state.  Measured:
      H(B_next | A_last), H(B_next | B_last), H(B_next | both) and their nulls.
"""
import csv, sys, os, collections, math, random
random.seed(9)
SRC_C, SRC_D = sys.argv[1], sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(HERE, "out")
def read(path):
    rows = []
    for r in csv.DictReader(open(path, encoding="utf-8-sig")):
        n = int(r["nClicks"]); icis = [int(round(float(r[f"ICI{i}"]) * 1000)) for i in range(1, n)]
        if n < 2 or any(x <= 0 for x in icis): continue
        rows.append(dict(type=r.get("CodaType", "?"), clan=r.get("Clan", "?"), icis=tuple(icis),
                         rec=r.get("REC", "")[:6], whale=int(float(r["Whale"])) if "Whale" in r else None,
                         t=float(r["TsTo"]) if "TsTo" in r else None))
    return rows
codas, dial = read(SRC_C), read(SRC_D)
def metre(i):
    m = min(i); return "".join('G' if round(x / m) >= 2 else 'L' for x in i)
def tempo_bin(i):
    T = sum(i) / 1000
    return 0 if T < 0.45 else 1 if T < 0.61 else 2 if T < 0.93 else 3 if T < 1.08 else 4
def H_cond(pairs):   # pairs of (context, next)
    ctx = collections.defaultdict(collections.Counter)
    for c, n in pairs: ctx[c][n] += 1
    N = len(pairs); H = 0.0
    for c in ctx.values():
        n = sum(c.values())
        for v in c.values(): H -= (v / N) * math.log2(v / n)
    return H

# ---------------------------------------------------------------- §G
print("§G  OBSERVABILITY QUOTIENT — bisimulation refinement of the empirical whale machine, readout = metre")
seqs = collections.defaultdict(list)
for c in sorted(dial, key=lambda c: (c["rec"], c["t"])):
    seqs[(c["rec"], c["whale"])].append((metre(c["icis"]), tempo_bin(c["icis"])))
succ = collections.defaultdict(set)
for s in seqs.values():
    for a, b in zip(s, s[1:]): succ[a].add(b)
states = sorted({x for s in seqs.values() for x in s})
# initial partition: by readout (metre); refine: two states equivalent iff same readout and same set of successor blocks
block = {s: s[0] for s in states}
while True:
    sig = {s: (block[s], frozenset(block[t] for t in succ[s])) for s in states}
    new = {}; ids = {}
    for s in states:
        new[s] = ids.setdefault(sig[s], len(ids))
    if len(set(new.values())) == len(set(block.values())): break
    block = new
classes = collections.defaultdict(list)
for s in states: classes[block[s]].append(s)
merged = [v for v in classes.values() if len(v) > 1]
metres_with_tempo_split = collections.Counter()
for m in {s[0] for s in states}:
    blocks_of_m = {block[s] for s in states if s[0] == m}
    metres_with_tempo_split[len(blocks_of_m)] += 1
print(f"  states (metre × tempo-bin) {len(states)}; readout classes (metres) {len({s[0] for s in states})}; "
      f"bisimulation classes {len(classes)}")
print(f"  metres whose tempo variants are all identified by their futures: {sum(1 for m in {s[0] for s in states} if len({block[s] for s in states if s[0]==m})==1)}; "
      f"metres split by tempo (future-distinguished): {sum(1 for m in {s[0] for s in states} if len({block[s] for s in states if s[0]==m})>1)}")
ex = [v for v in merged if len(v) >= 3][:5]
print("  examples of tempo variants identified by the quotient:", ex)
# the most frequent metres: are their tempo bins separated?
freq = collections.Counter(s for seq in seqs.values() for s in seq)
for m in ["GGLL", "LLLL", "LLL", "GLL"]:
    var = sorted({s for s in states if s[0] == m}, key=lambda s: s[1])
    print(f"  {m}: tempo bins present {[s[1] for s in var]} -> quotient blocks {[block[s] for s in var]}  (counts {[freq[s] for s in var]})")

# ---------------------------------------------------------------- §H
print("\n§H  REVERSAL — the ℤ/2 involution on codas; which readings are blind, and the repertoire's arrow of time")
ec1 = [c for c in codas if c["clan"] == "EC1" and "NOISE" not in c["type"]]
def rev(i): return tuple(reversed(i))
readings = {"click count": lambda i: len(i), "tempo (ms)": lambda i: sum(i), "mātrā": lambda i: sum(2 if s == 'G' else 1 for s in metre(i)),
            "guru count": lambda i: metre(i).count('G'), "metre": lambda i: metre(i), "exact shape": lambda i: i}
for name, f in readings.items():
    blind = sum(1 for c in ec1 if f(c["icis"]) == f(rev(c["icis"])))
    print(f"  {name:12} reversal-blind on {blind}/{len(ec1)} codas ({100*blind/len(ec1):.1f}%)")
pal = sum(1 for c in ec1 if metre(c["icis"]) == metre(rev(c["icis"])))
print(f"  fixed locus (palindromic metres): {pal}/{len(ec1)}")
mc = collections.Counter(metre(c["icis"]) for c in ec1)
print("  metre vs its reversal (counts): the arrow of time in the repertoire")
seen = set()
for m, k in mc.most_common(12):
    r = m[::-1]
    if m in seen or m == r: continue
    seen.add(m); seen.add(r); print(f"    {m:10} {k:5}   reversed {r:10} {mc.get(r,0):5}")

# ---------------------------------------------------------------- §I
print("\n§I  PRASNA — is B's run its answer stream?  B's next coda vs A's last (the answer) vs B's own last")
ordered = sorted(dial, key=lambda c: (c["rec"], c["t"]))
cls = lambda c: (metre(c["icis"]), tempo_bin(c["icis"]))
triples = []   # (A_last, B_last, B_next) with B_next by whale B, preceded (within 6 s) by A's coda and by B's own previous coda
by_key = collections.defaultdict(list)
for c in ordered: by_key[c["rec"]].append(c)
for rec, cs in by_key.items():
    for i, c in enumerate(cs):
        a_last = b_last = None
        for j in range(i - 1, -1, -1):
            if c["t"] - cs[j]["t"] > 6: break
            if cs[j]["whale"] != c["whale"] and a_last is None: a_last = cs[j]
            if cs[j]["whale"] == c["whale"] and b_last is None: b_last = cs[j]
        if a_last is not None and b_last is not None: triples.append((cls(a_last), cls(b_last), cls(c)))
N = len(triples)
H0 = H_cond([((), n) for a, b, n in triples]); HA = H_cond([(a, n) for a, b, n in triples]); HB = H_cond([(b, n) for a, b, n in triples]); HAB = H_cond([((a, b), n) for a, b, n in triples])
# nulls: shuffle the next coda
nxt = [n for a, b, n in triples]; random.shuffle(nxt)
HA0 = H_cond([(a, x) for (a, b, n), x in zip(triples, nxt)]); HB0 = H_cond([(b, x) for (a, b, n), x in zip(triples, nxt)]); HAB0 = H_cond([((a, b), x) for (a, b, n), x in zip(triples, nxt)])
print(f"  triples {N};  H(B_next) {H0:.3f} bits")
print(f"  H(B_next | A_last)  {HA:.3f}   (shuffled null {HA0:.3f})   — the answer alone")
print(f"  H(B_next | B_last)  {HB:.3f}   (shuffled null {HB0:.3f})   — B's own state alone")
print(f"  H(B_next | A_last, B_last) {HAB:.3f}   (shuffled null {HAB0:.3f})")
print(f"  information from the answer beyond B's own state: {HB - HAB:.3f} bits; from B's state beyond the answer: {HA - HAB:.3f} bits")
same_a = sum(1 for a, b, n in triples if n[0] == a[0]); same_b = sum(1 for a, b, n in triples if n[0] == b[0])
print(f"  B's next metre equals A's last metre: {same_a}/{N} ({100*same_a/N:.1f}%);  equals B's own last metre: {same_b}/{N} ({100*same_b/N:.1f}%)")
with open(os.path.join(OUT, "instrument_round_two.tsv"), "w") as f:
    f.write("instrument\tvalue\n")
    f.write(f"bisim_states\t{len(states)}\nbisim_classes\t{len(classes)}\nH_Bnext\t{H0:.4f}\nH_Bnext_given_A\t{HA:.4f}\nH_Bnext_given_B\t{HB:.4f}\nH_Bnext_given_AB\t{HAB:.4f}\n")
