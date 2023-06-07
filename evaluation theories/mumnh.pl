:- working_directory(_, '../code').
:-[main].

% Birth mother
axiom([+mum(diana,william)]).
% Step mother
axiom([+mum(camilla,william)]).
% Mother are unique
    axiom([-mum(\x,\z),-mum(\y,\z),+eq(\x,\y)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
trueSet([]).
falseSet([eq(diana,camilla), eq(diana,william), eq(camilla,william)]).

protect([eq,arity(eq)]).

theoryFile:- pass. 
