# Emit a native HVM4 search for a shortest word, from the already-emitted
# CubeDiameter runtime.  The search primitive is HVM4's own: one labelled
# superposition per word position, collapse enumerating the survivors.  No
# interpreter is written here; the runtime does the choosing.
#
#   bend CubeDiameter.bend --to-hvm4-full > CubeDiameter.hvm4
#   python3 emit_superposition_search.py CubeDiameter.hvm4 2 '@gU'
#   hvm search_2.hvm4 -s -C
import sys, os
BASE   = os.path.dirname(os.path.abspath(__file__))
EMIT   = sys.argv[1]          # the --to-hvm4-full output of CubeDiameter.bend
K      = int(sys.argv[2])     # word length searched
TARGET = sys.argv[3]          # an HVM4 expression, e.g. @gU or @superflip
src = open(EMIT).read().replace("@main = @GodsNumber", "// main replaced below")

L = []
faces = ["U","D","R","L","F","B"]
# 18 moves: face^1, face^2, face^3
L.append("// ---- the 18 face turns as group elements")
idx = 0
moves = []
for f in faces:
    L.append(f"@m{idx} = @g{f}")
    moves.append(idx); idx += 1
    L.append(f"@m{idx} = @compose(@g{f})(@g{f})")
    moves.append(idx); idx += 1
    L.append(f"@m{idx} = @compose(@compose(@g{f})(@g{f}))(@g{f})")
    moves.append(idx); idx += 1

L.append("// ---- a superposed choice of one move: distinct label per word position")
for i in range(K):
    nest = "&{}"
    for j in reversed(moves):
        nest = f"&L{i}{{#Pair{{{j}, @m{j}}}, {nest}}}"
    L.append(f"@pick{i} = {nest}")

L.append("// ---- the word: one superposed move per position, product accumulated")
for i in range(K):
    L.append(f"@p{i} = λ&g. λ&w. @step{i}(g)(w)(@pick{i})")
    L.append(f"@step{i} = λ&g. λ&w. λ{{#Pair: λ&j. λ&m. @p{i+1}(@compose(g)(m))(#Con{{j, w}})}}")
L.append(f"@p{K} = λ&g. λ&w. @keep(@eqElt(g)(@identity))(w)")
L.append("// ---- keep the word only when the product is the identity; else void it")
L.append("@keep = λ&b. λ&w. (λ{0: λ&w. &{}; _: λ&pred. λ&w. w})(b)(w)")
L.append(f"@main = @p0({TARGET})(#Nil)")
open(f"search_{K}.hvm4", "w").write(src + "\n" + "\n".join(L) + "\n")
print(f"search_{K}.hvm4  depth={K} target={TARGET}")
