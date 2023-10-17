:- working_directory(_, '../code').
:-[main].

theoryName(capOfnh).

axiom([+cap_of(london,britain)]).
axiom([+cap_of(edinburgh,britain)]).
%axiom([+cap_of(tokyo,japan)]).
%axiom([+cap_of(kyoto,japan)]).
axiom([-cap_of(\x,\y),-cap_of(\z,\y),+eqq(\x,\z)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:
trueSet([]).
falseSet([eqq(edinburgh,london), eqq(tokyo,kyoto), eqq(london,edinburgh), eqq(kyoto,tokyo)]).
protect([eqq, arity(eqq)]).
heuristics([]).

theoryFile:- pass. 
