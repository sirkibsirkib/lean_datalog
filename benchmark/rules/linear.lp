% Right-linear transitive closure. The recursive atom is leftmost and the
% step relation is the base relation, so a path of length k needs depth k:
% the fixpoint is as deep as the data is long, and layers are narrow.
t(X, Y) :- p(X, Y).
t(X, Z) :- t(X, Y), p(Y, Z).
