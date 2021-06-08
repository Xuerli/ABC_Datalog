:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].

axiom([-goodPrice(\x),+buyStock(\x)]).
axiom([-goodPrice(\x),-riskyCompany(\y),+dontBuyStock(\x)]).
axiom([-inFusion(\x,steel),+riskyCompany(\x)]).
axiom([-closing(\x,\y),+riskyCompany(\x)]).
axiom([-inFusion(\x,steel),-stong(steel),+notRiskyCompany(\x)]).
axiom([+goodPrice(acme)]).
axiom([+inFusion(acme,steel)]).
axiom([+strong(steel)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([buyStock(acme)]).
falseSet([dontBuyStock(acme)]).

protect([eqq,arity(eqq),acme,steel]).
heuristics([ noAxiomDele]).
