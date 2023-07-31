:- working_directory(_, '../code').
:-[main].

theoryName(sr1).


axiom([+mum2(diana,william,birth)]).
axiom([+mum(camilla,william,birth)]).

trueSet([mum(diana,william,birth)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
