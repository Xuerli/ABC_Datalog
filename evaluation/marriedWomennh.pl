:- working_directory(_, '../src').
:-[main].

logic(datalog).

theoryName(marriedWomennh).

axiom([-hadHusband(\x),+marriedWoman(\x)]).
axiom([-marriedWoman(\x),+notDivorced(\x)]).
axiom([+hasHusband(flor)]).
axiom([+hadHusband(leticia)]).
axiom([-divorced(\x),-notDivorced(\x)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([notDivorced(flor)]).
falseSet([notDivorced(leticia)]).
%
protect([]).
heuristics([]).

theoryFile:- pass. 
