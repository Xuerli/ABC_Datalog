:- working_directory(_, '../code').
:-[main].

theoryName(moreCapOf).

axiom([+capital_of(london,england)]).
axiom([+capital_of(edinburgh,england)]).
axiom([+capital_of(glasgow,scotland)]).
axiom([-capital_of(\x,\y),-capital_of(\z,\y),+eq(\x,\z)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:
trueSet([]).
falseSet([eq(edinburgh,london), eq(london,edinburgh), eq(edinburgh,glasgow), eq(glasgow,edinburgh), eq(london,glasgow), eq(glasgow,london)]).
protect([eq, arity(eq)]).
heuristics([]).

theoryFile:- pass. 
