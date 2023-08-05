:- working_directory(_, '../code').
:-[main].

theoryName(cr7alt).


axiom([-eq(\y,c1(\z))]).
axiom([+eq(\x,\x),+world(unstable)]).
axiom([+unrelated(c1(\z))]).



trueSet([]).
falseSet([world(unstable)]).
protect([]).
heuristics([]).

theoryFile:- pass.
