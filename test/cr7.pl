:- working_directory(_, '../code').
:-[main].

theoryName(cr7).


axiom([-eq(f(\y),g(\y,c1(d)))]).
axiom([+eq(f(\x),g(\z,\z)),+world(unstable)]).
axiom([-unrelated(c1(d))]).



trueSet([]).
falseSet([world(unstable)]).
protect([]).
heuristics([]).

theoryFile:- pass.
