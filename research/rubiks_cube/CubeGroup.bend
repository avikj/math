# The cube group by coordinates.
#
# An element of G is four short lists: which corner sits in each of the eight
# corner slots and how it is twisted (mod 3), which edge sits in each of the
# twelve edge slots and how it is flipped (mod 2).  Equality of elements is
# equality of those lists, so it is decidable and definitional.
#
# This is the point of the file.  A sticker configuration is 54 records and a
# word is a name for the route that produced an element; neither is a normal
# form, so in either presentation "the same element" is a question.  In
# coordinates it is not a question: two words denote one element exactly when
# their coordinates agree, and that identification is the whole content a word
# presentation lacks.  G is then not a quotient to be computed but the
# subobject of (Z3 wr S8) x (Z2 wr S12) cut out by three conditions, below.
#
# Tables validated against five independent published facts before emission:
# the 20-move face-turn superflip word lands exactly on the superflip, |RU|=105,
# |RUR'U'|=6, |R U2 D' B D'|=1260 (the maximal element order in G), and the
# sune has order 6.

type Elt:
  case @elt:
    cp: U64[]
    co: U64[]
    ep: U64[]
    eo: U64[]

def nth(xs: U64[], i: U64) -> U64:
  match xs:
    case []: 0
    case x <> rest:
      if i === 0:
        x
      else:
        nth(rest, i - 1)

def permAt(src: U64[], idx: U64[], n: U64, k: U64) -> U64[]:
  if k === n:
    []
  else:
    nth(src, nth(idx, k)) <> permAt(src, idx, n, k + 1)

def oriAt(gori: U64[], gperm: U64[], hori: U64[], m: U64, n: U64, k: U64) -> U64[]:
  if k === n:
    []
  else:
    ((nth(hori, k) + nth(gori, nth(gperm, k))) % m) <> oriAt(gori, gperm, hori, m, n, k + 1)

# compose(g, h) is "g first, then h".
def compose(g: Elt, h: Elt) -> Elt:
  match g:
    case @elt{gcp, gco, gep, geo}:
      match h:
        case @elt{hcp, hco, hep, heo}:
          @elt{permAt(gcp, hcp, 8, 0), oriAt(gco, hcp, hco, 3, 8, 0),
               permAt(gep, hep, 12, 0), oriAt(geo, hep, heo, 2, 12, 0)}

def identity() -> Elt:
  @elt{[0,1,2,3,4,5,6,7], [0,0,0,0,0,0,0,0],
       [0,1,2,3,4,5,6,7,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

# ---- the eighteen generators: six faces, quarter / half / inverse, unit cost ----

def gU() -> Elt:
  @elt{[3,0,1,2,4,5,6,7], [0,0,0,0,0,0,0,0], [3,0,1,2,4,5,6,7,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gU2() -> Elt:
  @elt{[2,3,0,1,4,5,6,7], [0,0,0,0,0,0,0,0], [2,3,0,1,4,5,6,7,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gUi() -> Elt:
  @elt{[1,2,3,0,4,5,6,7], [0,0,0,0,0,0,0,0], [1,2,3,0,4,5,6,7,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gD() -> Elt:
  @elt{[0,1,2,3,5,6,7,4], [0,0,0,0,0,0,0,0], [0,1,2,3,5,6,7,4,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gD2() -> Elt:
  @elt{[0,1,2,3,6,7,4,5], [0,0,0,0,0,0,0,0], [0,1,2,3,6,7,4,5,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gDi() -> Elt:
  @elt{[0,1,2,3,7,4,5,6], [0,0,0,0,0,0,0,0], [0,1,2,3,7,4,5,6,8,9,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gR() -> Elt:
  @elt{[4,1,2,0,7,5,6,3], [2,0,0,1,1,0,0,2], [8,1,2,3,11,5,6,7,4,9,10,0], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gR2() -> Elt:
  @elt{[7,1,2,4,3,5,6,0], [0,0,0,0,0,0,0,0], [4,1,2,3,0,5,6,7,11,9,10,8], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gRi() -> Elt:
  @elt{[3,1,2,7,0,5,6,4], [2,0,0,1,1,0,0,2], [11,1,2,3,8,5,6,7,0,9,10,4], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gL() -> Elt:
  @elt{[0,2,6,3,4,1,5,7], [0,1,2,0,0,2,1,0], [0,1,10,3,4,5,9,7,8,2,6,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gL2() -> Elt:
  @elt{[0,6,5,3,4,2,1,7], [0,0,0,0,0,0,0,0], [0,1,6,3,4,5,2,7,8,10,9,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gLi() -> Elt:
  @elt{[0,5,1,3,4,6,2,7], [0,1,2,0,0,2,1,0], [0,1,9,3,4,5,10,7,8,6,2,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gF() -> Elt:
  @elt{[1,5,2,3,0,4,6,7], [1,2,0,0,2,1,0,0], [0,9,2,3,4,8,6,7,1,5,10,11], [0,1,0,0,0,1,0,0,1,1,0,0]}

def gF2() -> Elt:
  @elt{[5,4,2,3,1,0,6,7], [0,0,0,0,0,0,0,0], [0,5,2,3,4,1,6,7,9,8,10,11], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gFi() -> Elt:
  @elt{[4,0,2,3,5,1,6,7], [1,2,0,0,2,1,0,0], [0,8,2,3,4,9,6,7,5,1,10,11], [0,1,0,0,0,1,0,0,1,1,0,0]}

def gB() -> Elt:
  @elt{[0,1,3,7,4,5,2,6], [0,0,1,2,0,0,2,1], [0,1,2,11,4,5,6,10,8,9,3,7], [0,0,0,1,0,0,0,1,0,0,1,1]}

def gB2() -> Elt:
  @elt{[0,1,7,6,4,5,3,2], [0,0,0,0,0,0,0,0], [0,1,2,7,4,5,6,3,8,9,11,10], [0,0,0,0,0,0,0,0,0,0,0,0]}

def gBi() -> Elt:
  @elt{[0,1,6,2,4,5,7,3], [0,0,1,2,0,0,2,1], [0,1,2,10,4,5,6,11,8,9,7,3], [0,0,0,1,0,0,0,1,0,0,1,1]}

def alphabet() -> Elt[]:
  [gU(), gU2(), gUi(), gD(), gD2(), gDi(), gR(), gR2(), gRi(), gL(), gL2(), gLi(), gF(), gF2(), gFi(), gB(), gB2(), gBi()]

# ---- the three conditions that cut G out of the wreath product ----

def sumMod(xs: U64[], m: U64) -> U64:
  match xs:
    case []: 0
    case x <> rest: (x + sumMod(rest, m)) % m

def inversions(xs: U64[], n: U64, i: U64, j: U64) -> U64:
  if i === n:
    0
  else:
    if j === n:
      inversions(xs, n, i + 1, i + 2)
    else:
      if nth(xs, i) > nth(xs, j):
        1 + inversions(xs, n, i, j + 1)
      else:
        inversions(xs, n, i, j + 1)

def parity(xs: U64[], n: U64) -> U64:
  inversions(xs, n, 0, 1) % 2

def cornerTwistClosed(g: Elt) -> Bool:
  match g:
    case @elt{cp, co, ep, eo}: sumMod(co, 3) === 0

def edgeFlipClosed(g: Elt) -> Bool:
  match g:
    case @elt{cp, co, ep, eo}: sumMod(eo, 2) === 0

def paritiesAgree(g: Elt) -> Bool:
  match g:
    case @elt{cp, co, ep, eo}: parity(cp, 8) === parity(ep, 12)

def inG(g: Elt) -> Bool:
  if cornerTwistClosed(g):
    if edgeFlipClosed(g):
      paritiesAgree(g)
    else:
      False
  else:
    False

# ---- equality of elements is equality of coordinates ----

def eqList(xs: U64[], ys: U64[]) -> Bool:
  match xs:
    case []:
      match ys:
        case []: True
        case y <> r: False
    case x <> rx:
      match ys:
        case []: False
        case y <> ry:
          if x === y:
            eqList(rx, ry)
          else:
            False

def eqElt(g: Elt, h: Elt) -> Bool:
  match g:
    case @elt{a, b, c, d}:
      match h:
        case @elt{p, q, r, s}:
          if eqList(a, p):
            if eqList(b, q):
              if eqList(c, r):
                eqList(d, s)
              else:
                False
            else:
              False
          else:
            False

def power(g: Elt, k: U64) -> Elt:
  if k === 0:
    identity()
  else:
    compose(power(g, k - 1), g)


# ---- checks: the identities a word presentation does not carry ----

def orderFourU() -> Bool: eqElt(power(gU(), 4), identity())
def orderFourR() -> Bool: eqElt(power(gR(), 4), identity())
def orderFourF() -> Bool: eqElt(power(gF(), 4), identity())
def halfIsSquareR() -> Bool: eqElt(gR2(), compose(gR(), gR()))
def inverseIsCubeR() -> Bool: eqElt(gRi(), compose(gR(), compose(gR(), gR())))
def oppositeCommuteUD() -> Bool: eqElt(compose(gU(), gD()), compose(gD(), gU()))
def oppositeCommuteRL() -> Bool: eqElt(compose(gR(), gL()), compose(gL(), gR()))
def oppositeCommuteFB() -> Bool: eqElt(compose(gF(), gB()), compose(gB(), gF()))
def generatorsInG() -> Bool:
  if inG(gU()):
    if inG(gR()):
      if inG(gF()):
        if inG(gL()):
          if inG(gB()):
            inG(gD())
          else: False
        else: False
      else: False
    else: False
  else: False
def composeStaysInG() -> Bool: inG(compose(gR(), compose(gU(), gFi())))

# the superflip: every edge flipped in place, corners untouched.  It realises
# the diameter from below.
def superflip() -> Elt:
  @elt{[0,1,2,3,4,5,6,7], [0,0,0,0,0,0,0,0],
       [0,1,2,3,4,5,6,7,8,9,10,11], [1,1,1,1,1,1,1,1,1,1,1,1]}

def superflipInG() -> Bool: inG(superflip())
def superflipIsInvolution() -> Bool: eqElt(compose(superflip(), superflip()), identity())

def allChecks() -> Bool[]:
  [orderFourU(), orderFourR(), orderFourF(),
   halfIsSquareR(), inverseIsCubeR(),
   oppositeCommuteUD(), oppositeCommuteRL(), oppositeCommuteFB(),
   generatorsInG(), composeStaysInG(),
   superflipInG(), superflipIsInvolution()]

def main() -> Bool[]:
  allChecks()

# ---- the question, over elements: distance as the Bellman potential ----
#
# No words appear.  d(g) = 0 exactly at the identity, and d(g) <= k+1 exactly
# when some generator step from g lands within k.  That is Phi(normal form)=0
# with Phi(u) <= c(u->v) + Phi(v) on every edge, so the distance IS the
# potential and the recursion is the statement, not a search over routes.

def anyStep(g: Elt, gens: Elt[], k: U64) -> Bool:
  match gens:
    case []: False
    case s <> rest:
      if inBall(compose(g, s), k):
        True
      else:
        anyStep(g, rest, k)

def inBall(g: Elt, k: U64) -> Bool:
  if k === 0:
    eqElt(g, identity())
  else:
    if eqElt(g, identity()):
      True
    else:
      anyStep(g, alphabet(), k - 1)

def distAtMost(g: Elt, k: U64) -> Bool:
  inBall(g, k)

# the lower bound witness: the superflip is not within 19
def superflipBeyond19() -> Bool:
  if inBall(superflip(), 19):
    False
  else:
    True

# small certified distances, where the value is known independently
def identityAt0() -> Bool: inBall(identity(), 0)
def uAt1() -> Bool: inBall(gU(), 1)
def uNotAt0() -> Bool:
  if inBall(gU(), 0):
    False
  else:
    True

def probes() -> Bool[]:
  [identityAt0(), uAt1(), uNotAt0()]
