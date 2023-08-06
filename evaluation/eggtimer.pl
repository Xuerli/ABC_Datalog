:- working_directory(_, '../code').
:-[main].

theoryName(eggtimer).

axiom([+meet(v1,l1,l2)]).
axiom([+meet(v2,l2,l3)]).
axiom([+meet(v3,l3,l4)]).
axiom([+meet(v4,l4,l1)]).
axiom([+meet(x,l1,l3)]).
axiom([-meet(\v1,\l1,\l2),-meet(\v2,\l2,\l3),-meet(\v3,\l3,\l4),-meet(\v4,\l4,\l1),-meet(\x,\l1,\l3),+polygon(eggtimer,set_of(\v1,\v2,\v3,\v4),set_of(\l1,\l2,\l3,\l4))]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([]).
falseSet([polygon(eggtimer,set_of(v1,v2,v3,v4),set_of(l1,l2,l3,l4))]).
protect([]).
heuristics([]).     %noAxiomAdd

theoryFile:- pass. 
