:- working_directory(_, '../code').
:-[main].

theoryName(cr3).


% axiom([-mum(\x,\y,\w),-mum(\z,\y,\w),+eq(\x,\z)]).
% axiom([+mum(qu(lily),qu(tina),birth)]).
% axiom([+mum(qu(lily),qu(victor),step)]).
% axiom([+mum(qu(anna),qu(victor),step)]).
axiom([+hi(hi32)]).
axiom([+eq(\x,qu(\y)),-hi(hi32)]).

trueSet([]).
falseSet([eq(qu(xx(anna)),qu(lily))]).
protect([eq]).
heuristics([]).

theoryFile:- pass.
