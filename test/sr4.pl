:- working_directory(_, '../code').
:-[main].

theoryName(sr4).

axiom([+crazy(x(\x)), +female(x(\x))]).
axiom([-honest(\y)]).
axiom([+mum(diana,william)]).
axiom([+mum(kate,george)]).

trueSet([female(x(kate))]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
