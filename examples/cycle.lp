% The same rules over a CYCLE. Saturation still terminates: every derivable
% atom lies in the finite Herbrand base, so the fixpoint is reached after
% all nine pairs have been derived.

edge(a, b).
edge(b, c).
edge(c, a).

path(X, Y) :- edge(X, Y).
path(X, Z) :- path(X, Y), edge(Y, Z).
