:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].

axiom([+cap_of(london,britain)]).
axiom([+cap_of(edinburgh,britain)]).
%axiom([+cap_of(tokyo,japan)]).
%axiom([+cap_of(kyoto,japan)]).
axiom([-cap_of(\x,\y),-cap_of(\z,\y),+eqq(\x,\z)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:
trueSet([]).
falseSet([eqq(edinburgh,london), eqq(tokyo,kyoto), eqq(london,edinburgh), eqq(kyoto,tokyo)]).
protect([eqq, arity(eqq),london,britain,edinburgh,tokyo,kyoto,japan]).
heuristics([ noRuleChange, noAnalogy, noPrecAdd, noAss2Rule, noAxiomDele, noVabWeaken, noPrecDele]).
