:- working_directory(_, '../code').
:-[main].

theoryName(naturals).
 
axiom([+naturals(0)]).
axiom([-naturals(\x),+naturals(suc(\x))]).

eqAxiom([suc(0),1]).
eqAxiom([suc(1),2]).

suc(X,Y):-
    Y is X + 1.

trueSet([]).
falseSet([naturals(2)]).
protect([]).
heuristics([]).

theoryFile:- pass.

