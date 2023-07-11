:- working_directory(_, '../code').
:-[main].

theoryName(vBargain).


axiom([-mark(\x,\y),-box(\y),+select(\x,\y)]).
axiom([+round(g1,1,2)]).
axiom([+round(g2,2,1)]).
axiom([+mark(g1,b1)]).
axiom([+mark(g2,b1)]).
axiom([+box(b1)]).
axiom([+box(b2)]).
axiom([+box(b3)]).


trueSet([select(g1,b1),select(g2,b2),select(g2,b3)]).
falseSet([select(g1,b2),select(g1,b3),select(g2,b1)]).
protect([]).
heuristics([]).

theoryFile:- pass.
