:- working_directory(_, '../code').
:-[main].

axiom([+haha(x)]).
axiom([+p2(\x,func(\x))]).

trueSet([p2(\x,\y)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
