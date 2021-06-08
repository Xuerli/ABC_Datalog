:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].


axiom([+parent(a,b)]).
axiom([+parent(a,c)]).
axiom([+parent(d,b)]).
axiom([+male(a)]).
axiom([+male(c)]).
axiom([+female(d)]).
axiom([+female(b)]).
axiom([+father(\x,\y),-parent(\x,\y),-male(\x)]).
axiom([+male(f)]).
axiom([+male(g)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([father(a,b),father(a,c),mother(d,b), father(f,a)]).
falseSet([mother(a,b),mother(a,c),father(d,b), father(g,a), father(g,c)]).
protect([]).
heuristics([]).
