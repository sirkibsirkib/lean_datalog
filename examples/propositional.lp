% Zero-arg atoms: the parens may be dropped, so `rain.` and `rain().` are
% the same atom. With no variables anywhere this is just propositional
% forward chaining.

rain.
sprinkler.

wet :- rain.
wet :- sprinkler.
slippery :- wet.
