// Numbers: zero and suc.  Order is defined by equations on them; min selects one of its two arguments.
le(zero, Y) = true;
le(suc(X), zero) = false;
le(suc(X), suc(Y)) = le(X, Y);
if(true, A, B) = A;
if(false, A, B) = B;
min(X, Y) = if(le(X, Y), X, Y);

// The finite set: empty is the unit of disjoint union.
union(empty, B) = B;
union(A, empty) = A;

// The least element, and the set without it: the meet over a union is the meet of the parts' meets.
least(one(X)) = X;
rest(one(X)) = empty;
least(union(A, B)) = min(least(A), least(B));
rest(union(A, B)) = which(least(union(A, B)), least(A), union(rest(A), B), union(A, rest(B)));

// which of two identified cells: the same cell, or not
which(X, X, P, Q) = P;
which(X, Y, P, Q) = Q;

// The ordered presentation of a finite set: its least element, then the presentation of the rest.
present(empty) = nil;
present(S) = cons(least(S), present(rest(S)));
