:- working_directory(_, '../code').
:-[main].

theoryName(cr3).


axiom([-mum(\x,\y,\w),-mum(\z,\y,\w),+eq(\x,\z)]).
axiom([+mum(lily,tina,birth)]).
axiom([+mum(lily,victor,step)]).
axiom([+mum(anna,victor,step)]).

trueSet([]).
falseSet([eq(anna,lily),eq(lily,anna)]).
protect([eq]).
heuristics([]).

theoryFile:- pass.
