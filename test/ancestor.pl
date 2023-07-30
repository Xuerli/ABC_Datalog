:- working_directory(_, '../code').
:-[main].

theoryName(ancestor).


axiom([-a(x),+b(x)]).
axiom([-b(x),+c(x)]).
axiom([-c(x),+a(x)]).
axiom([+a(x),+b(x),+c(x)]).

trueSet([]).
falseSet([a(x)]).
protect([]).
heuristics([]).

theoryFile:- pass.
