:- working_directory(_, '../code').
:-[main].

theoryName(workingStudenth).

axiom([+notworking(\x),-student(\x)]).
axiom([-undstudent(\x),+adult(\x)]).
axiom([-adult(\x),+working(\x)]).
axiom([+undstudent(lily)]).
axiom([-undstudent(\x),+student(\x)]).
axiom([-working(\x),-notworking(\x)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([undstudent(lily),  working(lily)]).
falseSet([]).
%
protect([lily,adult,arity(adult)]).
heuristics([ noAnalogy, noAss2Rule, noVabWeaken, noPrecDele]).

theoryFile:- pass.
