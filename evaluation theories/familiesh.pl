:- working_directory(_, '../code').
:-[main].

axiom([+parent(a,b,birth)]).
axiom([+parent(a,c,step)]).
axiom([+families(\x,\y), -parent(\x,\y,birth)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([families(a,b),families(a,c)]).
falseSet([]).
protect([a,b,c]).
heuristics([ noAss2Rule,noAxiomDele]).

theoryFile:- pass.
