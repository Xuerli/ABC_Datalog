:- working_directory(_, '../code').
:-[main].

theoryName(naturals).
 
axiom([+naturals(0)]).
axiom([-naturals(\x),+naturals(suc(\x))]).

eqAxiom([suc(0),1]).
eqAxiom([suc(1),2]).


trueSet([naturals(1),naturals(2)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.

