% Three variables, and on a chain no triangle exists — so this derives
% NOTHING while still enumerating |consts|^3 substitutions every tick. It
% isolates the cost that is driven by the constant universe rather than by
% the data or the answer.
tri(X, Z) :- p(X, Y), p(Y, Z), p(Z, X).
