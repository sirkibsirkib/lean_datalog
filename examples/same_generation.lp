% Non-linear recursion: the recursive atom sits in the MIDDLE of the body,
% so this cannot be evaluated by simply chasing one relation forwards.
%
% Two people are of the same generation if their parents are.
%
%           a           generation 0
%          / \
%         b   c         generation 1  ->  sg(b, c), sg(c, b)
%         |   |
%         d   e         generation 2  ->  sg(d, e), sg(e, d)
%
% Each arrow points from parent down to child. Siblings b and c are of the
% same generation because they share the parent a; d and e are because
% their parents b and c already are.

person(a).
person(b).
person(c).
person(d).
person(e).

parent(a, b).
parent(a, c).
parent(b, d).
parent(c, e).

sg(X, X) :- person(X).
sg(X, Y) :- parent(P, X), sg(P, Q), parent(Q, Y).
