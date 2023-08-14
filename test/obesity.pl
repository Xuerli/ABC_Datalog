:- working_directory(_, '../code').
:-[main].

theoryName(obesity).
 
axiom([+eat(ernest,icecream)]).
axiom([-eat(\x,icecream),+obese(\x)]).

trueSet([]).
falseSet([obese(ernest)]).
protect([]).
heuristics([]).

theoryFile:- pass.

