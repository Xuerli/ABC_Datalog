:- working_directory(_, '../code').
:-[main].

theoryName(moreMum).

% Birth mother
axiom([+mum(diana,william)]).
axiom([+mum(camilla,william)]).
axiom([+mum(diana,harry)]).
axiom([+stepMother(camilla,harry)]).
% Mother are unique
axiom([-mum(\x,\z),-mum(\y,\z),+eq(\x,\y)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
trueSet([]).
falseSet([eq(diana,camilla), eq(diana,william), eq(diana,harry)]).

protect([eq,arity(eq)]).

theoryFile:- pass. 
