:- working_directory(_, '../code').
:-[main].

theoryName(mumh).

% Birth mother
axiom([+mum(diana,william)]).
% Step mother
axiom([+mum(camilla,william)]).
% Mother are unique
axiom([-mum(\x,\z),-mum(\y,\z),+eq(\x,\y)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
trueSet([]).
falseSet([eq(diana,camilla), eq(diana,william), eq(camilla,william)]).


protect([eq,arity(eq),camilla, diana, william, prop(eq)]).
heuristics([ noRuleChange, noAnalogy, noAxiomDele, noPrecDele,noAxiomAdd]).

theoryFile:- pass.


% working_directory(_, 'C:/Users/turtleburrito/Documents/GitHub/ABC_Datalog/evaluation theories').