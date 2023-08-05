:- working_directory(_, '../code').
:-[main].

theoryName(cr6alt).


axiom([+white(\x),-swan(\x)]).
axiom([+swan(\x),+crazy(\x)]).
axiom([+european(\x),-german(\x)]).
axiom([+swan(lily)]).
axiom([+swan(lucy)]).
axiom([-crazy(bruce)]).
axiom([-german2(lily)]).
axiom([+german(lily)]).
axiom([+european(lucy)]).
axiom([-european2(bruce)]).
axiom([-crazy(lucy)]).
axiom([-crazy(lily)]).


trueSet([white(lily)]).
falseSet([white(bruce)]).
protect([]).
heuristics([]).

theoryFile:- pass.
