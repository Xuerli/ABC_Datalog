:- working_directory(_, '../code').
:-[main].

theoryName(cr1).


axiom([-mum(\x,\y),-mum(\z,\y),+eq(\x,\z)]).
axiom([+mum(lily,tina)]).
axiom([+mum(lily,victor)]).
axiom([+mum(anna,victor)]).

trueSet([]).
falseSet([eq(anna,lily),eq(lily,anna)]).
protect([eq]).
heuristics([]).

theoryFile:- pass.
