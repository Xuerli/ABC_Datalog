:- working_directory(_, '../code').
:-[main].

theoryName(cr6).


axiom([+white(\x),-swan(\x)]).
axiom([+european(\x),-german(\x)]).
axiom([+swan(lily)]).
axiom([+swan(lucy)]).
axiom([+swan(bruce)]).
axiom([+german(lily)]).
axiom([+european(lucy)]).
axiom([+australian(bruce)]).


trueSet([white(lily)]).
falseSet([white(bruce)]).
protect([]).
heuristics([]).

theoryFile:- pass.
