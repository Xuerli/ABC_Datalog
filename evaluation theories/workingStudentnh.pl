:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].


axiom([+notworking(\x),-student(\x)]).
axiom([-student(\x),+adult(\x)]).
axiom([-adult(\x),+working(\x)]).
axiom([+student(lily)]).
axiom([-working(\x),-notworking(\x)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([student(lily), adult(lily), working(lily)]).
falseSet([notworking(lily)]).
%
protect([]).
heuristics([]).
