:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].


axiom([+mammal(tweety)]).
axiom([+penguin(tweety)]).
axiom([+bird(tweety)]).
axiom([-bird(\x), +fly(\x)]).
axiom([-penguin(\y), +bird(\y)]).
axiom([-bird(\y), +feath(\y)]).
axiom([-mammal(\x),-bird(\x)]).

trueSet([feath(tweety),feath(tweety), fly(tweety)]).
falseSet([fly(tweety)]).



protect([]).
heuristics([]).
