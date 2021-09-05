:- working_directory(_, '/Users/lixue/GoogleDrive/publish/ACS/code').
:-[main].


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
protect([]).
heuristics([]).

theoryFile:- pass.
