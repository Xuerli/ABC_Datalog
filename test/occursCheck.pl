:- working_directory(_, '../code').
:-[main].

theoryName(occursCheck).

axiom([+haha(x)]).
axiom([+p2(\x,func(\x))]).

trueSet([p2(\x,\x)]). %Not allowed but simply for demonstrating occurs check.
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
