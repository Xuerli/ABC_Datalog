:- working_directory(_, '../code').
:-[main].

% axiom([+naturals(happy),+naturals(sad)]).
% axiom([-naturals(\x),+naturals(suc(\x,suc(suc(\y))))]).

axiom([+naturals(0)]).
axiom([-naturals(\x),+naturals(suc(\x))]).

suc(X,Y):-
    Y is X + 1.

trueSet([]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
