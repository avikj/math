ac or; idem or; unit or false;
or(true, R*) = true;
or(X, neg(X), R*) = true;
neg(true) = false;
neg(false) = true;
neg(neg(X)) = X;
X = false when neg(X) = true;
X = true  when neg(X) = false;
