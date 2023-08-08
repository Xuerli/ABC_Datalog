:- working_directory(_, '../code').
:-[main].

theoryName(eggtimer2).

axiom([+meet(v1,l1,l2)]).
axiom([+meet(v2,l2,l3)]).
axiom([+meet(v3,l3,l4)]).
axiom([+meet(v4,l4,l1)]).
axiom([+meet(x,l1,l3)]).
axiom([-eq(l1,l3)]).
axiom([-eq(l3,l1)]).
% More constraints on equality omitted...
axiom([+ls(l1)]).
axiom([+ls(l2)]).
axiom([+ls(l3)]).
axiom([+ls(l4)]).
axiom([-meet(\p,\l1,\l2),+vs(\p)]). %Equation 3
axiom([-vs(x),-ls(\l1),-ls(\l2),+eq(\l1,\l2),-meet(x,\l1,\l2),+polygon(eggtimer)]). %equation 1


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:
trueSet([]).
falseSet([polygon(eggtimer)]).
protect([ls,eq,arity(ls),arity(eq),[-vs(x),-ls(\l1),-ls(\l2),+eq(\l1,\l2),-meet(x,\l1,\l2),+polygon(eggtimer)]]).
heuristics([]).     %noAxiomAdd

theoryFile:- pass. 
