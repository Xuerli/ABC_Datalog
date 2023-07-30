:- working_directory(_, '../code').
:-[main].

theoryName(cr4).


axiom([+fly(\x),-bird(\x)]).
axiom([+bird(\y),-penguin(\x)]).
axiom([+penguin(lucy)]).


trueSet([]).
falseSet([fly(lucy)]).
protect([]).
heuristics([]).

theoryFile:- pass.
