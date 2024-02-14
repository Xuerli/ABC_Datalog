axiom([-a(\x),-notb(\x, \y), -new(\y), +c(\x)]).
axiom([+b(v1,pv2)]).
axiom([+a(v1)]).
axiom([+p1(pv1)]).
axiom([+p2(pv2)]).
axiom([-p1(\y) , -p2(\x), +new(\x)]).


:- working_directory(_, '../code').
:-[main].

trueSet([c(v1)]).
falseSet([]).
heuristics([]).

