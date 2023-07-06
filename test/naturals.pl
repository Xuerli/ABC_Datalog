:- working_directory(_, '../code').
:-[main].

theoryName(naturals).
 
axiom([+naturals(0)]).
axiom([-naturals(pre(\x)),+naturals((\x))]).

pre(X,Y):-
    Y is X - 1.

trueSet([naturals(1)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.

