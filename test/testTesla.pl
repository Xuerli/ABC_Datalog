:- working_directory(_, '../code').
:-[main].

theoryName(tesla).

axiom([-vehicle(\v), +lane(\v,right)]).
axiom([+vehicle(telsa)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([]).
falseSet([lane(telsa, right)]).
The protected item(s):[[arity(lane)],[lane]].
heuristics([]).