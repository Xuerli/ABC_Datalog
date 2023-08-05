:- working_directory(_, '../code').
:-[main].

axiom([+adult(\x, employed),-undergraduateStudent(\x)]).
axiom([+notworking(\x,partTime),-student(\x)]).
axiom([+student(\x),-undergraduateStudent(\x)]).
axiom([+undergraduateStudent(lily)]).
axiom([+working(\x),-adult(\x, employed)]).
axiom([-notworking(\x,fullTime),-working(\x)]).
axiom([+adult(\x, unemployed),-postgraduateStudent(\x)]).
axiom([+postgraduateStudent(iris)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([undergraduateStudent(lily),  working(lily)]).
falseSet([working(iris)]).
%
protect([]).
heuristics([]).

theoryFile:- pass.
