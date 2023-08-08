:- working_directory(_, '../code').
:-[main].

theoryName(cr3).

axiom([+hi(f(x))]).
axiom([+eq(\x,f(\y)),-hi(f(x))]).
axiom([+unrelated(f(lily))]).

trueSet([]).
falseSet([eq(anna,f(lily))]).
protect([eq]).
heuristics([]).

theoryFile:- pass.
