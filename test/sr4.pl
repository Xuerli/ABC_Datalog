:- working_directory(_, '../code').
:-[main].

theoryName(sr4).

axiom([+crazy(\x), +female(\x)]).
axiom([-honest(kate)]).
axiom([+mum(diana,william)]).
axiom([+mum(kate,george)]).

trueSet([female(kate)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
