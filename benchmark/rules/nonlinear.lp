% Non-linear transitive closure: paths compose with paths, so their length
% doubles each round and the fixpoint is only log-deep. Same answers as
% linear.lp, far fewer and far wider layers.
t(X, Y) :- p(X, Y).
t(X, Z) :- t(X, Y), t(Y, Z).
