:- working_directory(_, '../code').
:-[main].

theoryName(afterTweety).


axiom([+bird(\y,flightless),-penguin(\y)]).
axiom([+bird(polly,canFly)]).
axiom([+feather(\y),-bird(\y,\iv1)]).
axiom([+fly(\x),-bird(\x,canFly)]).
axiom([+kiwi(winky)]).
axiom([+penguin(tweety)]).

trueSet([feather(tweety),feather(polly), fly(polly), bird(winky,flightless)]).
falseSet([fly(tweety), fly(winky)]).


protect([]).
heuristics([]).

theoryFile:- pass.
