// ≤, by its identities: reflexive, transitive, antisymmetric, total.
le(X, X) = true;
le(X, Z) = true  when le(X, Y) = true, le(Y, Z) = true;
le(X, Y) = false when le(Y, X) = true, X # Y;
le(X, Y) = true  when le(Y, X) = false;
// the values: elem(n), n a finite set up to isomorphism
le(elem(X), elem(Y)) = nle(X, Y);
nle(zero, X) = true;
nle(suc(X), zero) = false;
nle(suc(X), suc(Y)) = nle(X, Y);
// conjunction
ac and; idem and; unit and true;
and(false, R*) = false;
