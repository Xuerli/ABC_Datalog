:- working_directory(_, '../code').
:-[main].

axiom([+bird(\y,flightless),-penguin(\y)]).
axiom([+bird(polly,canFly)]).
axiom([+feather(\y),-bird(\y,\iv1)]).
axiom([+fly(\x),-bird(\x,canFly)]).
axiom([+penguin(tweety)]).
axiom([+penguin(pingu)]).
axiom([+useTool(tweety, spoon)]).
axiom([+useTool(pingu, wing)]).
axiom([+fly(\x),-useTool(\x,wing)]).

trueSet([feather(tweety),feather(polly), fly(polly), fly(pingu)]).
falseSet([fly(tweety)]).


protect([feather,arity(feather),penguin, bird, arity(bird), arity(penguin), polly, pingu]).
heuristics([]).

theoryFile:- pass.
