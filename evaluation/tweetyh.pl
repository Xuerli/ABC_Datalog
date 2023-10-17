:- working_directory(_, '../code').
:-[main].

theoryName(tweetyh).

axiom([+penguin(tweety)]).
axiom([+bird(polly)]).
axiom([-bird(\x), +fly(\x)]).
axiom([-penguin(\y), +bird(\y)]).
axiom([-bird(\y), +feather(\y)]).

%Preferred Structure
trueSet([feather(tweety),feather(polly), fly(polly)]).
falseSet([fly(tweety)]).


%
protect([feather,arity(feather),penguin, mammal, arity(mammal), arity(penguin), polly, lucy]).
heuristics([ noRuleChange, noAnalogy, noPrecAdd, noAss2Rule, noAxiomDele, noVabWeaken, noPrecDele]).

theoryFile:- pass.
