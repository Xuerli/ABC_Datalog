axiom([+human(a1)]).
axiom([+human(a2)]).
axiom([+human(b1)]).
axiom([+human(b2)]).
axiom([+accident(x1,b1)]).
axiom([+accident(x2,b2)]).
axiom([+car(x1,autonomous)]).
axiom([+car(x2,non_autonomous)]).
%axiom([+car(x3,autonomous)]).
axiom([+check_injuries(vble(p),vble(q)),-accident(vble(x),vble(q)),-driver(vble(p),vble(x))]).
axiom([+driver(a1,x1)]).
axiom([+driver(a2,x2)]).
axiom([+legal_liable(vble(p),vble(x)),-driver(vble(p),vble(x))]).
axiom([+producer(x1,p1)]).
axiom([+producer(x2,p2)]).
%axiom([+producer(x3,p3)]).
:- working_directory(_, '/Users/xueli/Documents/code/cogAI_legal/ABC_Datalog-main/code').
:-[main].

trueSet([check_injuries(a1,b1), check_injuries(a2,b2),legal_liable(a2,x2),legal_liable(p1,x1)]).
%,legal_liable(p3,x3)
falseSet([legal_liable(a1,x1), legal_liable(p2,x2)]).
%exists_true([legal_liable(vble(p,x1)]).

heuristics([ noAxiomDele, noReform, noVabWeaken, noPrecDele]).
%expand([+[legal_liable,vble(z),vble(y)],-[car,vble(y),[autonomous]],-[producer,vble(y),vble(z)]])]


