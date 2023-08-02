:- working_directory(_, '../code').
:-[main].

theoryName(sr6).


axiom([+loves(\y,loveof(\y))]).
axiom([-loves(\x,\x),+world(stable)]).



trueSet([world(stable)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
