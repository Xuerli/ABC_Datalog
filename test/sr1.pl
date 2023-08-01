:- working_directory(_, '../code').
:-[main].

theoryName(sr1).


axiom([+mum2(q(diana),q(william),q(birth))]).
axiom([+mum(q(camilla),q(william),q(birth))]).

trueSet([mum(q(diana),q(william),q(birth))]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
