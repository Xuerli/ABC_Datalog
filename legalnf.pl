axiom([-a(\x),-notb(\x, \y), -new(\y), +c(\x)]).
axiom([+a(v1)]).
axiom([+p1(pv1)]).
axiom([+p2(pv2)]).
axiom([-p1(\y) , -p2(\x), +new(\x)]).


:- working_directory(_, '/Users/xueli/Documents/code/cogAI_legal/ABC_Datalog-main/code').
:-[main].

trueSet([]).
falseSet([c(v1)]).
heuristics([noReform,noAxiomDele]).

