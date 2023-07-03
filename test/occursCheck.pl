:- working_directory(_, '../code').
:-[main].

axiom([+haha(x)]).
axiom([+p2(\x,func(\y))]).

trueSet([p2(\x,\x)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
