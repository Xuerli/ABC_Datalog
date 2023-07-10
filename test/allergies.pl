:- working_directory(_, '../code').
:-[main].

theoryName(allergies).
 

axiom([-food(\x),+likes(john,\x)]).
axiom([+eats(carl,peanuts)]).
axiom([+alive(carl)]).
axiom([+eats(mary,peanuts)]).
axiom([+killed(mary)]).
axiom([+killed(\h),+alive(\h)]).
axiom([-killed(\g),-alive(\g)]).
axiom([-eats(\y,\z),+killed(\y),+food(\z)]).

trueSet([]).
falseSet([likes(john,peanuts)]). %John does not like peanuts because it killed his friend mary.
protect([]).
heuristics([]).

theoryFile:- pass.
