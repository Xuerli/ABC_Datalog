:- working_directory(_, '/Users/lixue/GoogleDrive/publish/ACS/code').
:-[main].

% Birth mother
axiom([+mum(diana,william)]).
axiom([+mum(lady_di,william)]).
% Step mother
axiom([+mum(camilla,william)]).
% Mother are unique
axiom([-mum(\x,\z),-mum(\y,\z),+eq(\x,\y)]).

trueSet([eq(diana,lady_di)]).
falseSet([eq(diana,camilla), eq(diana,william), eq(camilla,william)]).

protect([eq,arity(eq)]).
heuristics([]).

theoryFile:- pass. 
