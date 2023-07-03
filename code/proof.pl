
%% ABC Repair System Procedure %%
%% Xue Li Feb 2019 %%

%% This file contains the functions/predicates of dealing with proofs.
:- [util].
:- use_module(library(lists)).

/**********************************************************************************************
    unification(E1, E2, SigmaIn, UnisIn, UnisOut, SigmaOut, Result): Unify the equation E.
        Notice: The left side of the unification EL is the goal literal.
    Input:     E1 and E2 have to be two propositions: [P|Args]. Args vs Args will fail.
            SigmaIn: the applied substitutions.
            UnisIn = [], for keeping record of UnisOut.
    Output:    Unis: all unifications between terms or predicate symbols, e.g.,  [european=european, vble(x)=[lily]]
            SigmaOut: all of the applied substitutions.
            Result: [] if all equations success, or the remaining equations.
***********************************************************************************************/
unification(E1, E2, SigmaIn, UnisIn, UnisOut, SigmaOut, Result):- %/7
    pairwise([E1], [E2], Equations),
    unification(Equations, SigmaIn, UnisIn, UnisOut, SigmaOut, Result). %/6

unification([],Sigma, Unis, Unis, Sigma, []) :- !.   % Fail if failure wanted, but base case is successful

%Unification of two functions or two predicates.
unification([[F1|Args1]=[F2|Args2]|Old], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    F1==F2, !, length(Args1,L), length(Args2,L),       % If functors and arities agree
    pairwise(Args1, Args2, New),                   % Pair up corresponding subterms
    append(New, Old, Rest),                   % Add them to the Old problems
    unification(Rest, SigmaIn, [([F1|Args1]=[F2|Args2])|UnisIn], UnisOut, SigmaOut, UniResult).        % Repair either from recursive part

%Unification of two variables of the SAME name.
unification([vble(X)=vble(X)|Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-   % If two vars and same then
    !, unification(Rest, SigmaIn, [(vble(X)=vble(X))|UnisIn], UnisOut, SigmaOut, UniResult).                   % ignore them and carry on with the rest

%UNification of two variables of different names
unification([vble(X)=vble(Y)|Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    X\==Y, !,                                                    % If two vars are different then
    Subst1 = vble(Y)/vble(X),                                 % some subst needed
    compose1(Subst1,SigmaIn,SigmaMid),                        % Compose new substitution with old one
    subst(SigmaMid,Rest,NewRest),                             % substitute one for the other in the problems
    unification(NewRest, SigmaMid, [(vble(X)=vble(Y))|UnisIn], UnisOut, SigmaOut, UniResult).              % Recurse with new problem

%Unification of constant and constant
unification([A = B| Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    is_list(A), length(A, 1),  
    is_list(B), length(B, 1),                            
    A == B,
    unification(Rest, SigmaIn, [(A = B)|UnisIn], UnisOut, SigmaOut, UniResult).

%Unification of variable and constant
unification([A = B| Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    member(A = B, [(vble(X) = C), (C=vble(X))]),
    is_list(C), length(C, 1),!,                         % Constant is a constant
    Subst1 = C/vble(X),
    compose1(Subst1,SigmaIn,SigmaMid),                         % Compose new substitution with old one
    subst(SigmaMid,Rest,NewRest),
    unification(NewRest, SigmaMid, [(A = B)|UnisIn], UnisOut, SigmaOut, UniResult).

%Unification of variable and functions
unification([A = B| Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    member(A = B, [(vble(X) = C), (C=vble(X))]),
    is_list(C), length(C, Len),   
    Len > 1,
    occursCheck(X,C),!,                         
    Subst1 = C/vble(X),
    compose1(Subst1,SigmaIn,SigmaMid),                         % Compose new substitution with old one
    subst(SigmaMid,Rest,NewRest),
    unification(NewRest, SigmaMid, [(A = B)|UnisIn], UnisOut, SigmaOut, UniResult).

unification(Ununifiable,Sigma, Unis, Unis, Sigma, Ununifiable).        % the remaining failed unifications.

/**********************************************************************************************************************
    slRL(Goal, TheoryIn, EC, Proof, Evidence, Theorem): SL resolution based on refutation.
    Input:  Goal: Goal is the main goal, which could be a list of subgoals.
             TheoryIn is the input theory;
             EC is the equivalence classes.
            * CAUTION: each input clause is a Horn clause with its HEAD IN FRONT.
    Output: Theorem:         when there is positive literal in the input Goal, it could be a theorem derived in the end.
            Proof/Evidence:    either a Proof of Goal or an evidence of a failed proof, and the other is [].
            Proof/Evidence = [(Goal0, InputClause1, Subs1, Goal1, RemCondNum1), (Goal1, InputClause2, Subs2, Goal2, RemCondNum2), ...]
                    where Goal0 is the current goal clause,
                          InputClause1 is a clause that resolves the fist subgoal of Goal0;
                            Subs1 is a list of substitutions that applies to the arguments of InputClause1 in the proof/evidence;
                            Goal1 is the resulting goal clause of this derivation step which will be the goal to resolve in the nest step,
                            NumRemain is the number of the preconditions which originally come from InputClause1 and remain in the newest goal clause GoalX. For a proof, these numbers are 0.
    CAUTION: In a failed proof, it is the first subgoal cannot be resolved, and it is unknown whether the rest subgoals are resolvable or not.
************************************************************************************************************************/
% Nothing if the input theory is empty.
slRL(_, [], _, [], [], []):-!.

% Rewrite the input goal and the theory.
slRL(Goal, _, EC, _, _, _):-
    (\+is_list(Goal), nl,print('ERROR: slRL\'s Goal is not a list'),nl;
    \+is_list(EC), nl,print('ERROR: slRL\'s EC is not a list'),nl), fail, !.

% Rewrite the input goal and the theory.
slRL(Goal, TheoryIn, EC, Proof, Evidence, Theorem):-!,
    % Set an depth limit of the resoluton according to the length of the thoery.
    write_term_c("-----start slRL---------"),nl,
    length(TheoryIn, L),
    RCostLimit is L*L,    % the depth limit of a proof.
    %   % if there is a head in the goal clause, then move the head to the end, which is for the derivation of an assertion theorem.
    % (member(+Head, Goal) -> delete(Goal, +Head, RestGoal),
    %                         append(RestGoal, [+Head], GoalNew),!;
    % notin(+_, Goal) -> GoalNew = Goal),
    GoalNew = Goal, % There is no need to distinguish +/- now as everything needs to be resolved.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),
    write_term_c("GoalNew is "), write_term_c(GoalNew),nl,
    write_term_c("TheoryIn is "), write_term_c(TheoryIn),nl,
    write_term_c("EC is "), write_term_c(EC),nl,
    write_term_c("Proof  is uninitialized"), nl,
    write_term_c("Evidence is uninitialized"), nl,
    write_term_c("cost limit is "), write_term_c(RCostLimit),nl,
    slRLMain(GoalNew, [], TheoryIn, EC, ProofTem, EvidenceTem, Theorem, RCostLimit),
    write_term_c("-----end slRL---------"),nl,
    cleanSubMid(ProofTem, Proof),
    cleanSubMid(EvidenceTem, Evidence).

%% slRLMain1: No goals remain to resolve, a theorem is found, output the whole proof ([], Ancestors).
% When a proof is found, do not search further, and the evidence of partial proof is empty.
% This cases considers the goal becoming "=> P(x)" which is a theorem.
% slRLMain([+Literal], Evi, _, _, ProofOut, [], Theorem, _):- 
%     (Evi = [] -> ProofOut = [([+Literal],[],[],[+Literal],[0,0])]; % If Evidence is empty, theorem is proof
%      Evi = [_|_] -> ProofOut = Evi), % If evidence non-empty, theorem = proof
%     Theorem = [+Literal], !.
% NOTE : This is deleted as all positive literals need to be resolved as well.

%% slRLMain1: No goals to resolve, output the whole proof ([], Ancestors) with [] for Evidence and Theorem.
% When a proof is found, do not search further
slRLMain([], Proof, _,_, Proof, [], [],_):- !. % The proof is output. Reset the proofStatus to the default value 0.

%% slRLMain2: reorder subgoals in Goal by moving the first equality predicate to the end.
slRLMain(Goals, Deriv, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [-Equ| GRest],          % get the predicate of the left most sub-goal to resolve.
    Equ = [PG|_],
    member(PG, [=, \=]),% check if current goal is in the form of = or \=
     % if there is a variable in the sub-goal's arguments,
     % and not all of the goal predicates are equality/inequality predicate.
     % IF there are other predicates in the goal clause (IF not, this whole thing will be false.)
     setof(P, (member(-[P|_], GRest), notin(P, [=, \=])),_)->
        % move the equality or inequality to the end of the goal clause.
        % keep the positive literal in the end if there is one.
        (last(GRest, -_) ->
                    append(GRest, [-Equ], GoalsNew);
         last(GRest, +_) ->
                     reverse(GRest, [+P|GTail]),
                     reverse([+P| [-Equ| GTail]], GoalsNew)),
        updateDeriv(Deriv, reorder, DerivNew),    % update the derivation record.
         slRLMain(GoalsNew, DerivNew, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit).

%% slRLMain3.1: Use an input ASSERTION to resolve Goal which does not have = as its predicate.
% This resolves the current goal if there exists an input assertion +[P|Arg] that resolves -[P|Arg] directly.
slRLMain(Goals, Deriv, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [-[P| Arg]| GoalsRest],
    notin(P, [=, \=]),
    addAncestor(TheoryIn,Deriv,TheoryWithAncestor),
    (notin(vble(_), Arg)-> %The case where no variable is considered.
                member([+[P| Arg]], TheoryWithAncestor), % Find an exact match with all constants?
                InputClause = [+[P| Arg]],
                GoalsNew = GoalsRest,
                SG =[];
     occur(vble(_), Arg)->
                 member([+[P| Arg2]], TheoryWithAncestor), % find a match where the predicate name matches with any arguments
                 InputClause = [+[P| Arg2]], % Note: we are finding one that does not introduce additional goals.
                 unification([P| Arg], [P| Arg2], [],[],_, SG, []), %attempt unification of variables
                 print('substitution check'),nl,print(SG),nl,
                 subst(SG, GoalsRest, GoalsNew)), %Apply all substitutions from SG to GoalsRest.
    CurDerStep = ((Goals, SG), (InputClause, []), GoalsNew, [0, 0]), %Ref. 7.8 of thesis
    updateDeriv(Deriv, CurDerStep, firstNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    slRLMain(GoalsNew, DerivNew, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.

%% slRLMain3.2: Use a constraint theorem -[P|Arg] to resolve theorem +[P|Arg].
slRLMain(Goals, Deriv, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [+[P| Arg]| GoalsRest],
    notin(P, [=, \=]),
    addAncestor(TheoryIn,Deriv,TheoryWithAncestor),
    (notin(vble(_), Arg)-> %The case where no variable is considered.
                member([-[P| Arg]], TheoryWithAncestor), % Find an exact match with all constants?
                InputClause = [-[P| Arg]],
                GoalsNew = GoalsRest,
                SG =[];
     occur(vble(_), Arg)->
                 member([-[P| Arg2]], TheoryWithAncestor), % find a match where the predicate name matches with any arguments
                 InputClause = [-[P| Arg2]], % Note: we are finding one that does not introduce additional goals.
                 unification([P| Arg], [P| Arg2], [],[],_, SG, []), %attempt unification of variables
                 subst(SG, GoalsRest, GoalsNew)), %Apply all substitutions from SG to GoalsRest.
    CurDerStep = ((Goals, SG), (InputClause, []), GoalsNew, [0, 0]), %Ref. 7.8 of thesis
    updateDeriv(Deriv, CurDerStep, firstNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    slRLMain(GoalsNew, DerivNew, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.


%% slRLMain4: Use an input rule to resolve Goal which does not have == as its predicate.
%If goal is -
slRLMain(Goals, Deriv, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [-Goal| GoalsRest],
    Goal = [Pred| _],            % get the predicate of the left most sub-goal to resolve.
    notin(Pred, [=, \=]),    % Pred is not = neither \=.
    addAncestor(TheoryIn,Deriv,TheoryWithAncestor),
    %**Caution: any CUT here will cause the issue of unable to find all proofs even under findall/3. Therefore, a Flag proofStatus is applied.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),   % Set the proofStatus as 1, so the first sub-goal will be resolved if it can be.
    length(Deriv, RDepth),
    RDepth < RCostLimit,    % The current proof depth is not larger than the limit.
    % Require that the head of a clause should be its first literal. (This should be relaxed) + reordering
    findClause(+[Pred| _],TheoryWithAncestor,InputClause),
    reorderClause(+[Pred| _],InputClause,ReorderedClause),
    % rewrite the shared variable in Goals if that variable occurs both in the goal and the input clause.
    rewriteVble(Goals, ReorderedClause, RewClause, SubsVG), %Does not seem to be important, if input is properly "standardized apart". Skip.
    RewClause = [+[Pred| ArgCl]| Body], %This is from the input clause. Body is later appended into the other goals.
    % between two variables, SubsRes replace the goal's variable with the input clause's variable
    unification(Goal, [Pred| ArgCl], [],[],_, SubsRes, []),        % If successful resolution
    append(Body, GoalsRest, GoalsTem2),    % Get the resulting clause C with newly introduced literals Body in front.
    subst(SubsRes, GoalsTem2, GoalsNew),
    noTautology(GoalsNew),
    noloopBack(GoalsNew, Deriv),        % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),      % Reset the flag to the default value 0.
    %* Do not remove duplicated sub-goals which will effect trace-back process.
    length(Body, RemCondNum),            % the number of the remaining preconditions in the NewGoal.
    subDiv(SubsRes, Goals, SG),    % divide the substitutions to the ones applied to goal SG and the ones to the input clause SC.
    subDiv(SubsRes, InputClause, SI),
    compose1(SubsVG, SI, SubsCl),
    CurDerStep = ((Goals, SG), (InputClause, SubsCl), GoalsNew, [RemCondNum, 0]),
    updateDeriv(Deriv, CurDerStep, firstNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    slRLMain(GoalsNew, DerivNew, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.

%% slRLMain4: Use an input rule to resolve Goal which does not have == as its predicate.
% If goal is +
slRLMain(Goals, Deriv, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [+Goal| GoalsRest],
    Goal = [Pred| _],            % get the predicate of the left most sub-goal to resolve.
    notin(Pred, [=, \=]),    % Pred is not = neither \=.
    addAncestor(TheoryIn,Deriv,TheoryWithAncestor),
    %**Caution: any CUT here will cause the issue of unable to find all proofs even under findall/3. Therefore, a Flag proofStatus is applied.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),   % Set the proofStatus as 1, so the first sub-goal will be resolved if it can be.
    length(Deriv, RDepth),
    RDepth < RCostLimit,    % The current proof depth is not larger than the limit.
    % Require that the head of a clause should be its first literal. (This should be relaxed) + reordering
    findClause(-[Pred| _],TheoryWithAncestor,InputClause),
    reorderClause(-[Pred| _],InputClause,ReorderedClause),
    % rewrite the shared variable in Goals if that variable occurs both in the goal and the input clause.
    rewriteVble(Goals, ReorderedClause, RewClause, SubsVG),
    RewClause = [-[Pred| ArgCl]| Body], %This is from the input clause. Body is later appended into the other goals.
    % between two variables, SubsRes replace the goal's variable with the input clause's variable
    unification(Goal, [Pred| ArgCl], [],[],_, SubsRes, []),        % If successful resolution
    append(Body, GoalsRest, GoalsTem2),    % Get the resulting clause C with newly introduced literals Body in front.
    subst(SubsRes, GoalsTem2, GoalsNew),
    noTautology(GoalsNew),
    noloopBack(GoalsNew, Deriv),        % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),      % Reset the flag to the default value 0.
    %* Do not remove duplicated sub-goals which will effect trace-back process.
    length(Body, RemCondNum),            % the number of the remaining preconditions in the NewGoal.
    subDiv(SubsRes, Goals, SG),    % divide the substitutions to the ones applied to goal SG and the ones to the input clause SC.
    subDiv(SubsRes, InputClause, SI),
    compose1(SubsVG, SI, SubsCl),
    CurDerStep = ((Goals, SG), (InputClause, SubsCl), GoalsNew, [RemCondNum, 0]),
    updateDeriv(Deriv, CurDerStep, firstNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    slRLMain(GoalsNew, DerivNew, TheoryIn, EC, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.

%% slRLMain5: When there the firs sub-goal is irresolvable,return the evidence of the partial proof with [] as the proof and theorem.
%% Notice that only the first subgoal in Goals is gaurenteed to be unresolvable. The following subgoals could be resolvable.
slRLMain(Goals, Deriv, _, _, [], Evidence, [], _):-
    spec(proofStatus(1)),      % All axioms from the input theory have been tried for resolving the goal.
    Goals \= [],                    % And they all failed in resolving the remaining Goal.
    Goals \= [+_],                    % And it is not a derived assertion
    (Deriv = []-> Evidence = [(Goals, [], [], Goals, [0, 0])];    % record the unprovable goal when no RS have been done.
    Deriv \= []-> Evidence = Deriv),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))).   % The failed proof is output. Reset the proofStatus to the default value 0.


%% slRLMain5: resolve Goal whose predicate is \= based on UNAE.
%Resoluving equalities and inequalities.
slRLMain(Goals, Deriv, _, EC, Proof, Evidence, Theorem, RCostLimit):-
    forall(member(-[P|_], Goals), occur(P, [=, \=])),    % all of the goal predicates are equality/inequality predicates.
    % update the number of remaining goals fromtthe non-equality/non-inequality to equality/inequality.
    findall((RS, RSNew),
                (member(RS, Deriv),
                RS = (CG, Inp, GN, Sub, [Num1, Num2]),
                Num1 \= 0,
                N2New is Num1 + Num2,        % the remaining goal number is the sum of both type
                RSNew = (CG, Inp, GN, Sub, [0, N2New])),
            TypeUp),
    replace(TypeUp, Deriv, DerivNew),
    resolveEqu(Goals, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit).

/**********************************************************************************************************************
    resolveEqu(Goals, Derivation, EC, Proof, Theorem, RCostLimit):
            resolve the goals of equalities, after which resolve inequalities.
            When there is a variable, the instantiation choice of an equality is usually fewer than an inequality, so do it first.
    Input:  Goals: the list of subgoals to resolve.
            Derivation: a list of the previous derivation steps. For more infomation, please see updateDeriv.
            EC: the equivalence classes.
            RCostLimit: the limit of the length of the derivations.
    Output: Proof: the record of all derivation steps.
            Theorem: the derived theorem.
************************************************************************************************************************/
resolveEqu([], Proof, _, Proof, [], [], _):-!.
%    findall(E, (member((_,[+[= | Args]],_,_, ))).
resolveEqu([+P], Proof, _, Proof, [], [+P], _):-!.

resolveEqu(_, Evidence, _, [], Evidence, [], RCostLimit):-
    length(Evidence, RDepth),
    RDepth >= RCostLimit, !.        % The current proof depth has not bigger than the limit.

resolveEqu([-[=, X, Y]| GRest], Deriv, EC, Proof, Evidence, Theorem, RCostLimit):-
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),
    equalSub([=, X, Y], EC, Subs),
       % apply the substitution to the rest goal clause.
       subst(Subs, GRest, GoalsNew),
    noloopBack(GoalsNew, Deriv),      % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
     retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),
     CurDerStep = (([-[=, X, Y]| GRest], Subs), (unae, []), GoalsNew, [0, 0]),
     updateDeriv(Deriv, CurDerStep, secondNum, DerivNew),
     resolveEqu(GoalsNew, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit).

% resolve inequalities if there is no equalities left in the goal clause.
resolveEqu([-[\=|Args]| GRest], Deriv, EC, Proof, Evidence, Theorem, RCostLimit):-
    % check if there is no equalities left in the goal clause.
    notin(-[=|_], GRest),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),       % Set the proofStatus as 1, so the first sub-goal will be resolved if it can be.
    equalSub([\=|Args], EC, Subs),    % the inequality is true by appying substitution Subs.
    subst(Subs, GRest, GoalsNew),    % appying that substitution to the rest sub-goals.
    noloopBack(GoalsNew, Deriv),      % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
     retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),         % Reset the proofStatus flag to the default value 0.
     CurDerStep = (([-[\=|Args]| GRest],Subs), (unae, []), GoalsNew, [0, 0]),
     updateDeriv(Deriv, CurDerStep, secondNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    resolveEqu(GoalsNew, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.

% move inequalities to the end of the negative literals in the goal clause.
resolveEqu([-[\=|Args]| GRest], Deriv, EC, Proof, Evidence, Theorem, RCostLimit):-
    occur(-[=|_], GRest),    % not all of the goal predicates are inequality predicate.
    % move the equality or inequality to the end of the negative subgoals.
    % keep the positive literal in the end if there is one.
    (last(GRest, -[_]) ->
                append(GRest, [-[\=|Args]], GoalsNew);
     last(GRest, +[_]) ->
                 reverse(GRest, [+P|GTail]),
                 reverse([+P| [-[\=|Args]| GTail]], GoalsNew)),
    updateDeriv(Deriv, reorder, DerivNew),    % update the derivation record.
    resolveEqu(GoalsNew, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit).

%% When there the firs sub-goal is irresolvable,
%% return the evidence of the partial proof with [] as the proof and theorem.
%% Notice that only the first subgoal in Goals is guaranteed to be irresolvable. The following subgoals could be resolvable.
resolveEqu(Goals, Deriv, _, [], Evidence, [], _):-
    spec(proofStatus(1)),      % All axioms from the input theory have been tried for resolving the goal.
    Goals \= [],                    % And they all failed in resolving the remaining Goal.
    Goals \= [+_],                    % And it is not a derived assertion
    (Deriv = []-> Evidence = [(Goals, [], [], Goals, [0, 0])];    % record the unprovable goal when no RS have been done.
    Deriv \= []-> Evidence = Deriv),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))).      % The failed proof is output. Reset the proofStatus to the default value 0.


/**********************************************************************************************************************
    updateDeriv(DerivIn, ResStep, PredType, DerivOut):
            Update the record of the derivation steps.
    Input:  DerivIn: a list of the previous resolution steps, each of which is (Goal, InputClause, Subs, NextGoal, RemCondNum).
                InputClause: the input clause which resolves the first subgoal in Goal.
                Subs: the substitutions which have been applied to the InputClause.
                NextGoal: the resulting goal after resolvig with InputClause.
                RemCondNum: the remaining number of the preconditions of the InputClause in the last, newest Goal clause.
            ResStep: the last derivation step.
            PredType: the type of the predicate of the resolved subgoal: secondNum for = or \=, and firstNum for others.
    Output: DerivOut: the record of all derivation steps.
************************************************************************************************************************/
updateDeriv(Deriv, reorder, DerivNew):-
    findall(E,
            (member(E, Deriv),
             E = (_,  _, _, _, [0,0])),
            ES),
    deleteAll(Deriv, ES, DerivRemain),
    last(DerivRemain, Target),
    Target = (G1, Cl, S2, G2, [NumR1, NumR2]),
    NumR1New is NumR1 - 1,
    NumR2New is NumR2 + 1,
    TargetNew = (G1, Cl, S2, G2, [NumR1New, NumR2New]),
    replace(Target, TargetNew, Deriv, DerivNew).

updateDeriv(DerivIn, ResStep, PredType, DerivOut):-
    ResStep = ((G, SubG), (InputClause, SubCl), GoalsNew, Num),
    CurrentStep = (G, InputClause, SubCl, GoalsNew, Num),
    reverse(DerivIn, Deriv1),      % the update will start from the last InputClause.
    pairSub(G, SubG, GSPairs),    % get the list of pairs between a sub-goal and its new substitutions.
    updateOldCls(Deriv1, GSPairs, PredType, Deriv2),
    reverse([CurrentStep| Deriv2], DerivOut).    % make the derivation back in order.

updateOldCls([],_,_,[]):-!.
% Need to decrease the number of the remaining conditions of the inputclause which introduced the current resovled subgoal.
% H is the target RS which introduces the resolved subgoal.
updateOldCls([H|Rest], [(_, Subs)|RestPairs], PredType, [HNew| RestNew]):-
    H = (Goal, InputClause, SubOld, NextGoal, [RemNum1, RemNum2]),
    % update the number of the remaining preconditions of this rule in the current goal clause
    (PredType = firstNum, RemNum1 > 0 ->
        RemNum1New is RemNum1 - 1,
         NumUpd = [RemNum1New, RemNum2], !;
    PredType = secondNum, RemNum2 > 0 ->
        RemNum2New is RemNum2 - 1,
        NumUpd = [RemNum1, RemNum2New], !),
    compose1(Subs, SubOld, SubNew), !,   % the current substitutions are applied to this clause, so update Subs.
    HNew = (Goal, InputClause, SubNew, NextGoal, NumUpd),
    % update the substitutions.
    updatePreDer(Rest, RestPairs, RestNew).
% if the last branch fails, try this one.
updateOldCls([H|Rest], RestPairs, PredType, [H| RestNew]):-
    updateOldCls(Rest, RestPairs, PredType, RestNew).

% Supplement the substitution which applied to the latest resovaled subgoal to previous sub-goals that have not been fully resolved away.
% Do not need to decrease the number of the remaining conditions of the inputclause which introduced the current resovled subgoal.
updatePreDer([],_,[]):-!.
updatePreDer(All, [], All):- !.
updatePreDer([H|Rest], PairsIn, [HNew| RestNew]):-
    H = (Goal, InputClause, SubOld, NextGoal, [RemNum1, RemNum2]),
    RemCondNum is RemNum1 + RemNum2,
    % update the substitutions
    (RemCondNum > 0 ->
            PairsIn =[(_, Subs)|RestPairsNew],
            compose1(Subs, SubOld, SubNew),
            HNew = (Goal, InputClause, SubNew, NextGoal,  [RemNum1, RemNum2]), !;
     RemCondNum = 0 ->
            HNew = H, RestPairsNew = PairsIn),
    updatePreDer(Rest, RestPairsNew, RestNew).


/***************************************************************************************************************
    noloopBack(GoalsCur, Derivations):-
           Check if the current goals is no more complex than a previous goal in its own Proof.
           If yes, return true, otherwise, return false.
    Input:  GoalsCur: the current goal clause.
            Derivations is a list of derivation steps.
            Derivations = [(Goal, InputClause, SubNew, NextGoal, RemCondNum), ....]
****************************************************************************************************************/
noloopBack(_, []):- !.    % anygoal cannot cause a loop with the empty previous derivation.
noloopBack([], _):- !.    % empty goal clause could not cause a loop.
noloopBack(_, []):- !.
noloopBack(_, Deriv):-         % a loop is found when there is already an empty goal clause.
    member((_, _, _, [], _), Deriv), fail, !.
% The current goal is more complicated than a previous goal if all of the previous subgoals can be resolved with a proposition in the current goal.
noloopBack(GoalsCur, Deriv):-
    % Check for any previous goal PreGoal,
    (forall(member((_, _, _, PreGoal, _), Deriv),
            %there is a subgoal PreSubG which cannot be resolved with any subgoal in the current goal GoalCur.
            setof(PreSubG,
                    (member(-PreSubG, PreGoal),
                     % not resolvable with any current subgoal
                     forall(member(-CurSubG, GoalsCur),
                                unification(PreSubG, CurSubG, [], [], _, _, [_|_]))),
                      _))-> true, !;
     writeLog([nl, write_term_c('******** Error: Loop resolution ********'), nl,
            write_term_c('Current goal is: '), nl, write_term_c(GoalsCur), nl,
            write_term_c('The derivation steps are: '), nl,write_term_c(Deriv), finishLog]),fail).


/***************************************************************************************************************
    traceBackPos(TgtProp, Deriv, NegLit, InputClause, Subs):
            Find the original input clause which introduces the targeted proposition.
    Input:  Deriv is the derivation of a list of the resolution steps. For details, please see DerivIn in updateDeriv.
            Derivation = [(Goal, InputClause, Subs, NextGoal, RemCondNum), ...]
    Output: NegLit is the negative literal which introduces TgtProp.
               ClauseOri: the original input clause of NegProp.
    * InputClause is a Horn clause which has its positive literal as the head.
****************************************************************************************************************/
% Find the input clause which introduces the targeted proposition.
traceBackPos([P|ArgT], Deriv, NegLit, InputClause, Subs):-
    last(Deriv, CurResStep),
    CurResStep = (_, InputClause, Subs,_,_),
    setof(-[P|Arg],
            ( member(-[P|Arg], InputClause),
              unification([P|ArgT], [P|Arg],[],[],_,_,[])),
            [NegLit|_]), !.    % get the original negative literal.

% if it is the first step, then the targeted negative proposition is from preferred structure.
traceBackPos([P|ArgT], [(Goal, _,_,_,_)], NegLit, InputClause, Subs):-
    member(-[P| Argori], Goal),
    unification([P|ArgT], [P| Argori],[],[],_,Subs,[]), !,
    (Goal = [_|[_|_]] ->    % the original goal clause have at least two proposition, then it is a constran axiom from the input theory.
        NegLit = -[P|ArgT], InputClause = Goal;
     Goal = [-_] -> InputClause = [], NegLit= -[P|ArgT]).    % Otherwise, it comes from the preferred structure.

% otherwise, try the ancestors.
traceBackPos(TargProp, Deriv, NegLit, InputClause, Subs):-
    dropTail(Deriv, Ances),    % try the ancestors.
    traceBackPos(TargProp, Ances, NegLit, InputClause, Subs).


/***************************************************************************************************************
    traceBackC(C, Deriv, NegLit, InputClause, Subs):
            Find the original input clause which introduces the targeted constant.
    Input:  C: the target constant, e.g., [c].
            Deriv is the derivation of a list of the resolution steps. For details, please see DerivIn in updateDeriv.
            Derivation = [(Goal, InputClause, Subs, NextGoal, RemCondNum), ...]
    Output: Clause is the source of that constant, which can be a goal clause or a input clause.
    * InputClause is a Horn clause which has its positive literal as the head.
****************************************************************************************************************/
% Find the input clause which introduces the targeted proposition.
traceBackC(C, [([+[P|Args]], [],[],[+[P|Args]],[0,0])], [+[P|Args]]):-
    member(C, Args), !.
traceBackC(C, Deriv, Clause):-
    Deriv = [(Goals,InputCl,_,_,_)| _],
    % Try if c comes from the goal clause over the head of the input clause.
    findall(Prop, (member(-Prop, Goals), occur(C, Prop)), Props),
    (Props \= [], Clause = Goals, !;
     Props = []->
         (% try if c comes from the body of the input clause.
         findall(Prop2, (member(-Prop2, InputCl), occur(C, Prop2)), Props2),
         Props2 \= [], Clause = InputCl, !;
        last(Deriv, GoalLast),
        findall(PropL, (member(-PropL, GoalLast), occur(C, PropL)), Propsl),
        (Propsl \= [], Flag = true;
         Props = []-> Flag = false),
        traceBackCTail(C, Deriv, Flag, Clause))).    % get the original negative literal.

traceBackCTail(_, [], []):- fail, !.

traceBackCTail(C, Deriv, Flag, Output):-
    last(Deriv, (Goals,InputClause,_,_,_)),
    findall(Prop, (member(-Prop, Goals),occur(C, Prop)), Props),
    (Props = [], ( Flag == true ->  InputClause = Output, !; % find the last goal which does not contain the target, so the input clause in this step introduces the target.
                  Flag == false ->
                      dropTail(Deriv, Ances), !,    % try the ancestors.
                    traceBackCTail(C, Ances, false, Output));        % the target constant has gone from the goal clause previously.
    Props \= [],( Flag == true    ->
                    dropTail(Deriv, Ances), !,    % try the ancestors.
                    traceBackCTail(C, Ances, true, Output);            % the target constant has occured.
                  Flag == false ->
                    dropTail(Deriv, Ances), !,    % try the ancestors.
                    traceBackCTail(C, Ances, true, Output))).

/*********************************************************************************************************************************
    allTheoremsP(Theory, P, EC,Theorems): get all theorems whose predicate is P. P is neither = nor \=.
    Input:  Theory: the input theory.
            P: the targeted predicate.
    Output: Theorems is a list of theorem whose argument contains the constant.
**********************************************************************************************************************************/
allTheoremsP([], _, _,[]):- !.
allTheoremsP(TheoryIn, P, EC, AllTheorems):-
    notin(P, [=, \=]),
    % find all proofs of an equality, where Proof is the list of all proofs.
    findall(([+[P| ArgsS]], Proof),
            (% get an axiom whose head predicate is P
             member([+[P| Args]|Body], TheoryIn),
             Axiom = [+[P| Args]|Body],
             delete(Axiom, +[P| Args], Body),
             (% if it has no body, which means that it is an axiom of P.
              Body = [] -> % if it is equality, sort the arguments and ignore X=X.
                    (P = (=)-> sort(Args, ArgsS), length(ArgsS, L), L>1; ArgsS = Args),
                  Proof = [([-[P| ArgsS]], [+[P| ArgsS]], [], [], [0, 0])];
              % if it has a body, which means that it is a rule.
              Body \= [] ->
                  % get the equality theorems which can be derived from that rule.
                  slRL(Axiom, TheoryIn, EC, Proof, [], Theorem),
                  % remove the dupliate, and then ignore X=X by checking the number of arguments.
                  Theorem = [+[P| ArgsT]],
                  (P = (=)->sort(ArgsT, ArgsS), length(ArgsS, L), L>1;
                              ArgsS = ArgsT))),
            AllT),

    % remove duplicates.
    mergeTailSort(AllT, AllTheorems),
    writeLog([write_term_c('-- The theorems of Predicate -'), write_term_c(P),
            write_term_c('-- are:'),nl, write_term_c(AllTheorems), finishLog]).

/*********************************************************************************************************************************
    allTheoremsC(Theory, EC, Constant, Theorems): get all theorems whose arguments include the targeted constant.
    * Inequality only between constants at the same position in arguments of predicates.
    Input:  Theory: the input theory.
            EC: the equivalence class.
            Constant: the targeted constant, e.g., [c].
    Output: Theorems is a list of theorem whose argument contains the constant.
**********************************************************************************************************************************/
allTheoremsC([], _, _, []):- !.
allTheoremsC(Theory, EC, Constant, Theorems):-
    spec(signature(Sig, _)),
    findall(C2s, (member((_,_,ArgsDomains), Sig),
                member(ArgD1, ArgsDomains),
                delete(ArgD1, Constant, C2s),
                C2s \= ArgD1),
            C2S),
    flatten(C2S, IneqCands),
    % find all therems that can be derived starting with an axiom of the targeted costant.
    findall(Theorem,
            (% Get an assertion, +[P| Arugs], from the input theory.
                 member([+[P| Args]], Theory),
                 member(Constant, Args),
                 linkTheorems([+[P| Args]], Constant, Theory, EC, Theorems),
                 member(Theorem, Theorems)),
            TheoTem1),
    % find all therems that can be derived starting with the = or \= of the targeted costant.
    findall(Theorem,
            (    % Get the inequalities of Cconstant
                 findall([+[\=, [C2], Constant]],
                        (member(C2, IneqCands),
                        equalSub([\=, Constant, vble(x)], EC, [[C2]/vble(x)])),
                        Ineqs),
                % Get the equalities of Cconstant
                 findall([+[=, [C2], Constant]],
                         (equalSub([=, Constant, vble(x)], EC, [[C2]/vble(x)]),
                          [C2] \= Constant),
                         Eqs),
                 append(Ineqs, Eqs, EAll),
                 member(Ineq, EAll),
                 linkTheorems(Ineq, Constant, Theory, EC, Theorems),
                 member(Theorem, [Ineq| Theorems])),
            TheoTem2),

    % get all theorems that can be derived by a rule whose head has the targeted constant.
    findall(Theorem,
            (% Get a rule from the input theory.
                member(Clause, Theory),
                member(+[_| Arg], Clause),
                member(Constant, Arg),
                % Get all theorems that can be derived from this rule.
                slRL(Clause, Theory, EC, _, [], Theorem),
                % Check that the targeted constant occur in the arguments of the theorems.
                Theorem = [+[_| Cons]],
                occur(Constant, Cons)),
            TheoTem3),
    append(TheoTem1, TheoTem2, TheoTem),
    append(TheoTem, TheoTem3, TheoremsRaw),
    % remove duplicates
    sort(TheoremsRaw, Theorems).

/*********************************************************************************************************************************
    linkTheorems(TheoremIn, Constant, Theory, EC,TheoremsOut): get all theorems derived from TheoremIn.
    Input:  TheoremIn: a theorem whose argument contains the constant.
            Theory: the input theory.
            EC: the equivalence classes.
            Constant: the targeted constant, e.g., [c].
    Output: TheoremsOut is a list of theorems whose argument contains the constant.
**********************************************************************************************************************************/
linkTheorems([+[P| Args]], Constant, Theory, EC, [Theorem| Theorems]):-
    member(Constant, Args),
    % Get a rule from the input theory.
    member(Clause, Theory),
    member(-[P| Arg2], Clause),
    % The assertion can potentially resolve a precondition of that rule.
    unification([P| Args], [P| Arg2], [],[],_, Substitution, []),        % If successful resolution
    delete(Clause, -[P| Arg2], ClauseRest),                             % Get the resulting clause C with newly introduced literals Body in front.
    subst(Substitution, ClauseRest, ClauseRest2),
    slRL(ClauseRest2, Theory, EC, _, [], Theorem),

    % Check that the targeted constant occur in the arguments of the theorems.
    Theorem = [+[_| Cons]],
    member(Constant, Cons), !,
    linkTheorems(Theorem, Constant, Theory, EC, Theorems).

linkTheorems(_, _, _, _, []).

/**********************************************************************************************************************
    subDiv(SubsList, Clause, SG):
            Among SubsList, get the substitutions that applied to the goal clause (SG).
    Input: SubsList: a list of substitutions
           Clause: the clause
    Output: SG: the substitutions that applied to the clause (SG).
************************************************************************************************************************/
subDiv([],_,[]):-!.
subDiv(SubsList, Clause, SG):-
    findall(vble(X),
            (member(-[_|Args], Clause),    % omit the head as all variables in the head also occur in the boody in Datalog.
             member(vble(X),Args)),
            GVbles),
    findall((A/B),
            (member((A/B), SubsList),
            member(B, GVbles)),
            SGRaw),
    sort(SGRaw, SG).

/**********************************************************************************************************************
    pairSub(Goal, SubsList, SGPairs):
            get the pairs between a sub-goal and its substitutions that applied to that sub-goal
    Input: SubsList: a list of substitutions
           Goal: the goal clause
    Output: SGPairs=[(-[a,vble(x),vble(y)], [[c]/vble(x), [d]/vble(y)]),...]
************************************************************************************************************************/
pairSub([],_,[]):-!.
pairSub([SubG1| RestG], SubG, [(SubG1, SG1)| PRest]):-
    subDiv(SubG, [SubG1], SG1),
    pairSub(RestG, SubG, PRest).

/**********************************************************************************************************************
    cleanSubMid(Proof, ProofClean): delete the mid substitutions from each RS.
    Input: Proof: a list of resolution steps.
    Output: ProofClean: a list of resolution steps where mid substitutions are deleted.
************************************************************************************************************************/
cleanSubMid([], []):-!.
cleanSubMid([RS| Rest], [RSC| RestC]):-
    RS = (G, InpClause, Sub, GN, Num),
    (Sub = []-> RSC = RS;
     Sub = [_|_]->
    findall(vble(X),
            (member(-[_|Args], InpClause),    % omit the head as all variables in the head also occur in the boody in Datalog.
             member(vble(X), Args)),
            Vbles),
    findall((A/B),
            (member((A/B), Sub),
             member(B, Vbles)),
            NewSubRaw),
    sort(NewSubRaw, NewSub),
    RSC    = (G, InpClause, NewSub, GN, Num)),
    cleanSubMid(Rest, RestC).
