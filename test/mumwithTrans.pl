:- working_directory(_, '../code').
:-[main].

theoryName(mumWithTrans).


axiom([+mum(diana,william)]).
axiom([+mum(camilla,william)]).
% Mother are unique
axiom([-mum(\x,\z),-mum(\y,\z),+eq(\x,\y)]).
% properties of equality
axiom([-eq(\x,\y),+eq(\y,\x)]).
axiom([-eq(\x,\z),-eq(\y,\z),+eq(\x,\y)]).

trueSet([]).
falseSet([eq(diana,camilla), eq(diana,william)]).