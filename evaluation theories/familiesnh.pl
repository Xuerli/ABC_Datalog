:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].

axiom([+parent(a,b,birth)]).
axiom([+parent(a,c,step)]).
axiom([+families(\x,\y), -parent(\x,\y,birth)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([families(a,b),families(a,c)]).
falseSet([]).
protect([]).
heuristics([]).
