:- working_directory(_, '../code').
:-[main].

% axiom([+naturals(happy),+naturals(sad)]).
% axiom([-naturals(\x),+naturals(suc(\x,suc(suc(\y))))]).

axiom([+naturals(0)]).
axiom([-naturals(pre(\x)),+naturals((\x))]).

pre(X,Y):-
    Y is X - 1.

trueSet([naturals(1)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.

