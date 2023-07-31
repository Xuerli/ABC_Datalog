:- working_directory(_, '../code').
:-[main].

theoryName(sr5).


axiom([-p2(\x),+p5(\y),+p1(\x,\y)]).
axiom([-p3(\z),-p4(\z),+p2(\z)]).
axiom([+p3(a)]).
axiom([+p4(a)]).

trueSet([p1(a,b)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
