:- working_directory(_, '../src').
:-[main].

logic(datalog).

theoryName(superPenguinh).

axiom([-penguin(\x),+bird(\x)]).
axiom([-bird(\x),+fly(\x)]).
axiom([-superPenguin(\x),+penguin(\x)]).
%axiom([-superPenguin(\x),+fly(\x)]).
axiom([+superPenguin(opus)]).
axiom([+brokenWing(opus)]).
axiom([-brokenWing(\x),-bird(\x),+cannotFly(\x)]).
axiom([-fly(\x),-cannotFly(\x)]).

trueSet([fly(opus)]).
falseSet([cannotFly(opus)]).


protect([opus,fly,arity(fly), bird]).
heuristics([ noAnalogy, noAss2Rule, noVabWeaken, noPrecDele, noAssAdd]).

theoryFile:- pass.
