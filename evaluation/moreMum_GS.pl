:- working_directory(_, '../code').
:-[main].

% Birth mother
axiom([+mum(diana,william)]).
axiom([+stepMother(camilla,william)]).
axiom([+mum(diana,harry)]).
axiom([+stepMother(camilla,harry)]).
% Mother are unique
axiom([-mum(\x,\z),-mum(\y,\z),+eq(\x,\y)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
trueSet([]).
falseSet([eq(diana,camilla), eq(diana,william)]).

protect([eq,arity(eq)]).

theoryFile:- pass. 
