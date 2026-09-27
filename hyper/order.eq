// ≤, by its identities: reflexive, transitive, antisymmetric, total.
le(X, X) = true;
le(X, Z) = true  when le(X, Y) = true, le(Y, Z) = true;
le(X, Y) = false when le(Y, X) = true, X # Y;
le(X, Y) = true  when le(Y, X) = false;

// The values: each is elem(n), n a finite set up to isomorphism, zero and suc.
le(elem(X), elem(Y)) = nle(X, Y);
nle(zero, X) = true;
nle(suc(X), zero) = false;
nle(suc(X), suc(Y)) = nle(X, Y);

if(true, A, B) = A;
if(false, A, B) = B;
