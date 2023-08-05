:- working_directory(_, '../code').
:-[main].

theoryName(sr2alt).


axiom([+female(\x),-mum(\x,william)]).
axiom([+mum(diana,william)]).
axiom([+mum(kate,george)]).
% axiom([+female(georgesquare)]).

trueSet([female(kate)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
