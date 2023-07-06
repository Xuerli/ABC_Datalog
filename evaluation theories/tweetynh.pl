:- working_directory(_, '../code').
:-[main].

theoryName(tweetynh).

axiom([+penguin(tweety)]).
axiom([+bird(polly)]).
axiom([-bird(\x), +fly(\x)]).
axiom([-penguin(\y), +bird(\y)]).
axiom([-bird(\y), +feather(\y)]).

trueSet([feather(tweety),feather(polly), fly(polly)]).
falseSet([fly(tweety)]).



protect([]).
heuristics([]).

theoryFile:- pass.
