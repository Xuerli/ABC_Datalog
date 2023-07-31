:- working_directory(_, '../code').
:-[main].

theoryName(sr4).

axiom([-mum(\x,\y), +mum3(\x,\y)]).
% axiom([-mum2(diana,\x), +female(\x)]).
axiom([+mum(diana,william)]).
axiom([+mum(kate,george)]).

trueSet([female(kate)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
