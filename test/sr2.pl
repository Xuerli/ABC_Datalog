:- working_directory(_, '../code').
:-[main].

theoryName(sr2).


axiom([+female(\x),+mum(k(\x),k(william))]).
axiom([-mum(k(diana),k(george))]).
axiom([-mum(k(kate),k(george))]).
% axiom([+female(georgesquare)]).

trueSet([female(kate)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
