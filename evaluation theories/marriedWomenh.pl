:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].

axiom([-hadHusband(\x),+marriedWoman(\x)]).
axiom([-marriedWoman(\x),+notDivorced(\x)]).
axiom([+hasHusband(flor)]).
axiom([+hadHusband(leticia)]).
axiom([-divorced(\x),-notDivorced(\x)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([notDivorced(flor)]).
falseSet([notDivorced(leticia)]).
%
protect([flor,leticia]).
heuristics([ noAnalogy, noAss2Rule, noVabWeaken, noPrecDele]).
