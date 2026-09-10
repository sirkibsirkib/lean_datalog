% Transitive closure of a chain a -> b -> c -> d -> e.

edge(a, b).
edge(b, c).
edge(c, d).
edge(d, e).

path(X, Y) :- edge(X, Y).
path(X, Z) :- path(X, Y), edge(Y, Z).
