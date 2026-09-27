// A bag: the sum of the singletons of a list's elements.
ac union; unit union empty;
bag(nil) = empty;
bag(cons(X, R)) = union(one(X), bag(R));

// Sorted: a sequence whose each element is less than all following.
below(X, empty) = true;
below(X, one(Y)) = le(X, Y);
below(X, union(one(Y)*)) = and(le(X, Y)*);
least(one(X)) = X;
least(union(one(X), R*)) = X when below(X, union(R*)) = true;
without(one(X), X) = empty;
without(union(one(X), R*), X) = union(R*);
present(empty) = nil;
present(S) = cons(least(S), present(without(S, least(S)))) when S # empty;

main = present(bag(input));
