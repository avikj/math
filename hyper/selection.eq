// Selection sort, as declared: for each position i, the position of the least element at positions ≥ i is
// swapped with i.
sort(A) = sel(A, p0);
sel(A, end) = A;
sel(A, I) = sel(swap(A, I, argmin(A, I)), next(I)) when I # end;

argmin(A, end) = end;
argmin(A, I) = pick(A, I, argmin(A, next(I))) when I # end;
pick(A, I, end) = I;
pick(A, I, J) = if(le(at(A, I), at(A, J)), I, J) when J # end;

at(swap(A, I, J), K) = if(eq(K, I), at(A, J), if(eq(K, J), at(A, I), at(A, K)));
eq(X, X) = true;
eq(X, Y) = false when X # Y;

out(A, end) = nil;
out(A, I) = cons(at(A, I), out(A, next(I))) when I # end;
main = out(sort(input), p0);
