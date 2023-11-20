

:- use_module(library(lists)).
:-[preprocess, equalities, repairPlanGen, repairApply, vitality, fileOps].
    % clear all assertions. So main has to be compiling before the input theory file.
:-    maplist(retractall, [trueSet(_), falseSet(_), heuristics(_), protect(_), spec(_)]).

/********************************************************************************************************************** Global Variable and their values.
debugMode:    0 -- no write_term_c information.
            1 -- write_term_c informaiton.
spec(pft(:        the true set of the preferred structure in the internal format.
spec(pff:        the false set of the preferrd structure in the internal format.
costLimit:    the maximum length of the repair plans.
Signature:  [predicateInfoList, ConstantLists], where
            predicateInfoList = [(predsymbol, Arity Info, Arguments Domain), ...]
            Arity Info:  [(arity1, source1), (arity2, source2)], e.g., mum, [(3, theory), (2, prefStruc)].
            Arguments Domain: [[c11,c12..], [c21, c22,..]...], where [c11,c12..] is a list of constants occur as the first argument of that predicate in all theorems of P.
proofStatus:  0 -- default value.
            1 -- will get an axiom for resolving the goal, but there is no more axiom in the input theory.
            2 -- a positive literal is derived.
**********************************************************************************************************************/

:-dynamic pause/0.
%:-spy(pause).
pause.

abc:-
        current_predicate(exists_true, 1),
        exists_true(ET),
        ET \= [],
        ET = [Prop], !,
        convertClause([+Prop], [+Clause]),
        assert(outputFile_No_Last(0)),
        % Initialisation
        supplyInput,
        % Initialision: the theory, the preferred structure, the signature, the protected items and Equality Class and Inequality Set.
        initTheory(Theory),    % clear previous data and initialise new ones.
        precheckPS,

        spec(signature(_, Constants)), % Constants = [[camilla], [diana], [william]]
        findall( Clause_New,
                (
                 % replace the variable with a constant
                 member(vble(X), Clause),
                 member(C, Constants),
                 replace(vble(X), C, Clause, Clause_New),
                 outputFile_No_Last(Last),
                 OutputFile_No is Last + 1,

                 % clear previous data and initialise new ones.
                 retractall(spec(_)),
                 initTheory(Theory),

                 % it should not in the false set.
                 spec(pff(FalseSet)),
                 notin([+Clause_New], FalseSet),

                 spec(pft(TrueSet)),
                 append(TrueSet, [+Clause_New], TrueSetNew),
                 print('\nthe current TrueSetNew is '),
                 print(TrueSetNew),

                 retractall(spec(pft(_))),
                 retractall(outputFile_No_Last(_)),
                 assert(spec(pft(TrueSetNew))),
                 assert(outputFile_No_Last(OutputFile_No)),

                 abc_core(Theory, OutputFile_No)),
        _).


abc:-
         % Initialisation
        supplyInput,
        % Initialision: the theory, the preferred structure, the signature, the protected items and Equality Class and Inequality Set.
        initTheory(Theory),    % clear previous data and initialise new ones.
        precheckPS,
        abc_core(Theory,"1").

abc_core(Theory, OutputFile_No):-
    % setup log
    print('ok'),
    initLogFiles(StreamRec, StreamRepNum, StreamRepTimeNH, StreamRepTimeH),
    %statistics(walltime, [_ | [ExecutionTime1]]),
    statistics(walltime, [S,_]),

    % writeLog([nl,write_term_c('--------------executation time 1---'), nl,write_term_c('time takes'),nl, write_term_c(ExecutionTime1),nl]),
    % repair process
    detRep(Theory, AllRepStates),
    writeLog([nl,write_term_c('--------------AllRepStates: '),write_term_All(AllRepStates),nl, finishLog]),

    statistics(walltime, [E,_]),
    ExecutionTime is E-S,

    writeLog([nl,write_term_c('--------------executation time 2---'),
                nl,write_term_c('time takes'),nl, write_term_c(ExecutionTime),nl]),
    %ExecutionTime is ExecutionTime1 + ExecutionTime2,
    output(AllRepStates, ExecutionTime, OutputFile_No),
    maplist(close, [StreamRec, StreamRepNum, StreamRepTimeNH, StreamRepTimeH]),
    nl, print('-------------- Finish. --------------'), nl.

/**********************************************************************************************************************
    detRep(Theory, RepTheories):
            detect faults of the objective theory based on preferred structure and UNAE and repair it.
    Input:  Theory: the object theory.
    Output: AllRepSolutions is a list of [(Repairs, TheoryRepaired),....],
            where Repairs is the list of repairs applied to Theory resulting TheoryRepaired.
************************************************************************************************************************/
detRep(Theory, AllRepSolutions):-
    findall(TheoryRep,
            (% calculate equivalence classes, and then detect and repair the unae faults.
            unaeMain(Theory,  OptimalUnae),
            member((TheoryState, InsufIncomp), OptimalUnae),

            InsufIncomp = (_,INSUFF,ICOM), % Insufficiency and Incompatibility faults here. 1. sufficiencies, 2. insufficienies, 3. incompatability
            length(INSUFF,InsuffNum),
            length(ICOM,IncompNum),
            assert(spec(faultsNum(InsuffNum, IncompNum))),

             (InsufIncomp = (_,[],[])-> % if 2 and 3 are empty then it is fault free
                     TheoryRep = ([fault-free, 0, TheoryState]);    % if the theory is fault free.
             % Otherwise, repair all the faults and terminate with a fault-free theory or failure due to out of the costlimit.
              InsufIncomp \= (_,[],[])->
                      repInsInc(TheoryState, 0, InsufIncomp, TheoryRep))),
            AllRepTheos1),
    % Only select the minimal repairs w.r.t. the number of repair plans.
    spec(heuris(Heuristics)),
    (notin(minicost, Heuristics)->AllRepTheos1 = AllRepSolutions;
    member(minicost, Heuristics),
    findall((Len, Rep),
                (member(Rep, AllRepTheos1),
                 Rep = [_,_ ,[[RepPlans,_]|_]],
                 length(RepPlans, Len)),
            AllRepTheos2),
    length(AllRepTheos2, L222),
    writeLog([nl, write_term_c(L222), write_term_c(' AllRepTheos2 is:------'), nl,write_term_All(AllRepTheos2),nl,finishLog]),
    sort(AllRepTheos2, [(MiniCost, _)|_]),
    writeLog([nl, write_term_c(' MiniCost is:------'), nl,write_term_c(MiniCost),nl,finishLog]),

    setof(RepState, member((MiniCost, RepState), AllRepTheos2), AllRepSolutions)).

/**********************************************************************************************************************
    detInsInc(TheoryState, FaultState)
            detect sufficiencies and faults of insufficiencies, incompatibilities of the objective theory based on preferred structure.
    Input:  TheoryState = [[Repairs, BanRs], EC, EProof, TheoryIn, TrueSetE, TrueSetE], where:
            Theory is the current theory.
            Repairs is the repairs that have been applied to get the current theory.
            BanRs is the repairs that have been banned to apply, e.g., the ones failed in applying or violates some constrains.
            TrueSetE/FalseE: the true/false set of the preferred structure where all constants have been replaced by their representatives.
    Output: FaultState = (Suffs, InSuffs, InComps), where
                        Suffs: the provable goals from pf(T).
                        InSuffs: the unprovable goals from pf(T).
                        InComps: the provable goals from pf(F).
************************************************************************************************************************/
detInsInc(TheoryState, FaultState):-
    TheoryState = [RsRec, EC, _, Theory, TrueSetE, FalseSetE],
    writeLog([nl, write_term_c('---------Start detInsInc, Input theory is:------'), nl,
    nl,write_term_c(Theory),nl,write_term_All(Theory),nl,finishLog]),
    % Find all proofs or failed proofs of each preferred proposition.
    findall( [Suff, InSuff],
            ( % Each preferred sentence is negated, and then added into Theory.
              member([+[Pre| Args]], TrueSetE),
              % skip equalities/inequalities which have been tackled.
              notin(Pre, [\=, =]),
              Goal = [-[Pre| Args]],

              % Get all proofs and failed proofs of the goal.

              findall( [Proof, Evidence],
                     ( slRL(Goal, Theory, EC, Proof, Evidence, [])),
                     Proofs1),
              % Proofs1= [[P1, []],[P2, []],[[],E1]...]; Proofs2 = [[P1,P2,[]],[[],[],E]]
              transposeF(Proofs1, [Proofs, Evis]),
              % only collect none empty proofs/evidences
              (Proofs = []-> Suff = [], InSuff =(Goal, Evis);
               Proofs = [_|_]->Suff =(Goal, Proofs), InSuff=[])),
           AllP),
     % Split into a list of sufficiencies (Suffs), and a list of insufficiencies (InSuffs).
     transposeF(AllP, [Suffs, InSuffs]),

     writeLog([nl, write_term_c('---------SufGoals is------'), nl,write_term_c(Suffs),
     nl, write_term_c('---------InsufGoals is------'), nl,write_term_c(InSuffs), finishLog]),

    % detect the incompatibilities
      findall((Goal, UnwProofs),
           (member([+[Pre| Args]], FalseSetE),
            % skip equalities/inequalities which have been tackled.
            notin(Pre, [\=, =]),
            Goal = [-[Pre| Args]],
            % get all of a proof of Goal
            findall(Proof,
                    slRL(Goal, Theory, EC, Proof, [], []),
                    UnwProofsT),
            sort(UnwProofsT,UnwProofs),    % get rid of duplicates.
            UnwProofs \= []),    % Detected incompatibility based on refutation.
           InComps),             % Find all incompatibilities.

    writeLog([nl, write_term_c('---------InComps are------'),nl, write_term_All(InComps), finishLog]),
    % detect the inconsistencies due to the violation of constrains
    findall((Constrain, UnwProofs),
              (member(Constrain, Theory),        % get a constrain axiom from the theory.
               notin(+_, Constrain),
               findall(Proof,
                        slRL(Constrain, Theory, EC, Proof, [], []),
                        UnwProofs),
                UnwProofs \= []),
          Violations),
      writeLog([nl, write_term_c('---------Violations are------'),nl, write_term_All(Violations), finishLog]),
    append(InComps, Violations, Unwanted),
    FaultState = (Suffs, InSuffs, Unwanted),
    append(InSuffs, Unwanted, InitialAna),
    (RsRec = [[],[]], InitialAna = [] -> print('The input theory is fault-free.'), !;true).
/**********************************************************************************************************************
    repInsInc(TheoryState, Layer, FaultState, TheoryRep):
            return a repaired theory w.r.t. one fault among the FaultStates by applying an Parento optimal repair.
    Input:  TheoryState = [[Repairs, BanRs], EC, EProof, TheoryRep, TrueSetNew, FalseSetNew],
                            for more information, please see unaeMain.
            FaultState = (Suffs, InSuffs, InComps), for more information, please see detInsInc.
            Layer: the layer of repInsInc.
    Output: TheoryRep=[faulty/fault-free, Repairs, TheoryOut]
            Repairs: the repairs which have been applied to achieving a fault-free theory.
            TheoryOut: the fault-free theory which is formalised by applying Repairs to the input theory.
************************************************************************************************************************/
% If there is no faults in the theory, terminate with the fault-free theory.
repInsInc(TheoryState, Layer, (_, [], []), [fault-free, (Layer/N),  TheoryState]):-
    writeLog([nl,write_term_c('******** A solution is reached. *******'),nl]), !,
    TheoryState = [[RepPlans,_]|_],
    length(RepPlans, Len),
    spec(repNum(StreamRepNum)),
    write(StreamRepNum, Len),
    write(StreamRepNum, ', '), write(StreamRepNum, TheoryState),nl(StreamRepNum),nl(StreamRepNum),
    spec(roundNum(N)).%TheoryState = [[Repairs,_], _, _, TheoryRep, _, _], !.

% If the cost limit is reached, terminate with failure.
repInsInc(TheoryState, Layer, (_, Insuf, Incomp), [fault, (Layer/N), TheoryState]):-
    TheoryState = [[Repairs,_], _, _, _, _, _],
    costRepairs(Repairs, Cost),
    spec(costLimit(CostLimit)),
    spec(roundLimit(RoundLimit)),
    spec(roundNum(N)),
    retractall(spec(roundNum(_))),
    NewN is N+1,
    assert(spec(roundNum(NewN))),
    (Cost >= CostLimit; RoundLimit \= 0, N >= RoundLimit), !,
    write_term_c('******** Cost Limit is reached. *******'),nl,
    writeLog([nl, write_term_c('******** Cost Limit is reached. *******'),nl,
        write_term_c('Cost is: '), write_term_c(Cost), write_term_c('; Round: '), write_term_c(N),
        write_term_c('---------The current faulty TheoryState is------'), nl,write_term_All(TheoryState),
    nl, write_term_c('---------The remaining inffuficiencies are------'), nl,write_term_All(Insuf),
    nl, write_term_c('---------The remaining incompatibilities are------'), nl,write_term_All(Incomp), finishLog]).


% repair theory
repInsInc(TheoryStateIn, Layer, FaultStateIn, TheoryRep):-
    spec(roundNum(R)),
    writeLog([nl, write_term_c('--------- Start repInsInc round: '), write_term_c(R),nl, finishLog]),
    FaultStateIn = (SuffsIn, InsuffsIn, IncompsIn),
    TheoryStateIn = [_,_, _, TheoryIn, _, _],
    findall(Proof, (member((_, UnwProofs), IncompsIn), member(Proof, UnwProofs)),  IncompsProofs),

    appEach(InsuffsIn, [repairPlan, TheoryStateIn, SuffsIn], RepPlans1),
    appEach(IncompsProofs, [repairPlan, TheoryStateIn, SuffsIn], RepPlans2),
    append(RepPlans1, RepPlans2, RepPlans),
    % RepPlans = [RepPlan1|RepPlans2],
    length(RepPlans, RepPlansLen),
    writeLog([nl, write_term_c(RepPlansLen),write_term_c(' fault\'s new repair plans found: '), write_term_c(RepPlans), nl,nl,nl,write_term_c(TheoryIn),nl, finishLog]),

    repCombine(RepPlans, TheoryIn, RepSolutions),

    appEach(RepSolutions, [appRepair, TheoryStateIn], RepStatesTem),
    %print('000000'),print(RepStatesTem),nl,nl,print('RepStatesTem'),nl,nl,
    sort(RepStatesTem, RepStatesAll),
    length(RepStatesAll, LengthO),
    writeLog([nl, write_term_c('-- There are '), write_term_c(LengthO),
                  write_term_c(' repaired states: '),nl,write_term_All(RepStatesAll), nl, finishLog]),
    % prune the redundancy.
    mergeRs(RepStatesAll, RepStatesFine, TheoryIn),
    length(RepStatesFine, LengthFine),
    writeLog([nl, write_term_c('-- There are '), write_term_c(LengthFine),nl,
    write_term_c('RepStatesFine: '),nl,write_term_All(RepStatesFine), finishLog]),
    %print('111111 RepStatesFine'),print(RepStatesFine),nl,nl,
    findall((FNum1, FNum2, RepState, FaultStateNew),
                    (member(RepState, RepStatesFine),
                      detInsInc(RepState, FaultStateNew),
                      FaultStateNew = (_, InSuffNew, InCompNew),
                      length(InSuffNew, FNum1),
                      length(InCompNew, FNum2)),
             AllRepStates),
    length(AllRepStates, Length),
    writeLog([nl, write_term_c('-- All faulty states: '), write_term_c(Length),nl,
                write_term_All(AllRepStates), finishLog]),

     % pruning the sub-optimal.
    pareOpt(AllRepStates, Optimals1),
    length(Optimals1, LO1),
    writeLog([nl, write_term_c('--The number of Optimals: '), write_term_c(LO1), nl, write_term_All(Optimals1), finishLog]),
    % pruning the sub-optimal based on the vitality.
    % vitalityOpt(AllRepStates, Optimals2),
    % length(Optimals2, LO2),
    % writeLog([nl, write_term_c('--The number of Vitality Optimals: '), write_term_c(LO2), nl, write_term_All(Optimals2), finishLog]),
    %
    % subtract(Optimals1, Optimals2, In1Not2),
    % subtract(Optimals2, Optimals1, In2Not1),
    % length(In1Not2, LO3),
    % length(In2Not1, LO4),
    %
    % writeLog([nl, write_term_c('--The solution in 1 not in 2 include: '), write_term_c(LO3), nl, nl, write_term_All(In1Not2), finishLog]),
    % writeLog([nl, write_term_c('--The solution in 2 not in 1 include: '), write_term_c(LO4), nl, nl, write_term_All(In2Not1), finishLog]),
    %

    % get one optimal repaired theory along with its remaining faults and applied repairs Rep.
    member((TheoryStateOp, FaultStateOp), Optimals1),
    NewLayer is Layer+1,
    repInsInc(TheoryStateOp, NewLayer, FaultStateOp, TheoryRep).

/**********************************************************************************************************************
    pareOpt(StatesFaultsAll, OptStates):
            return a repaired theory w.r.t. one fault among the FaultStates by applying an Parento optimal repair.
    Input:  StatesFaultsAll is a list: [(FNum1, FNum2, TheoryState, FaultState),...]
    Output: OptStates is also a list of (TheoryState, FaultState) by pruning the sub-optimals.
            For more information about TheoryState/FaultState, please see detInsInc.
************************************************************************************************************************/
pareOpt([], []).
% if the sub-optimal pruning is not applied, return the input.
pareOpt(StatesFaultsAll, TheoryStateOut):-
    spec(heuris(H)),
    member(noOpt, H),
    findall([FNum, (TheoryState, FaultState)],
            (member((N1, N2, TheoryState, FaultState), StatesFaultsAll),
             FNum is N1 +N2),
            TheoryStateTem),
    sort(TheoryStateTem, TheoryStateTem2),
    transposeF(TheoryStateTem2, [_, TheoryStateOut]),!.

pareOpt(StatesFaultsAll, OptStates):-
    %writeLog([nl, write_term_c('--------- Pruning the sub-optimals with Threshod: '), write_term_c(Theres), nl, finishLog]),
    findall((TheoryState1, FaultState1),
            (member((NumF11, NumF12, TheoryState1, FaultState1), StatesFaultsAll),
             TheoryState1 = [[Rs1, _]|_],
             length(Rs1, NumR1),
             Cost1 is NumR1 + NumF11 + NumF12,
             forall((member((NumF21, NumF22, TheoryState2, _), StatesFaultsAll),
                      TheoryState2 = [[Rs2, _]|_],
                     length(Rs2, NumR2),
                     Cost2 is NumR2 + NumF21 + NumF22),
                    (%writeLog([nl, write_term_c('Cost1 & Cost2 is ---------'),nl,write_term_c(Cost1), write_term_c(Cost2), finishLog]),
                      Cost2 >= Cost1)),
             writeLog([nl, write_term_c('An Optimal repaired theory with cost:'), write_term_c(Cost1),
             write_term_c(' and the fault state: '), write_term_c(FaultState1), nl, write_term_c(TheoryState1), finishLog])),    % The repaired theory is not strictly dominated by any others.
            OptStates).

/**********************************************************************************************************************
    vitalityOpt(StatesFaultsAll, OptStates):
            return a repaired theory w.r.t. one fault among the FaultStates by only selecting the optimal based on vitality scores
    Input:  StatesFaultsAll is a list: [(FNum1, FNum2, TheoryState, FaultState),...]
    Output: OptStates is also a list of (TheoryState, FaultState) by pruning the sub-optimals.
            For more information about TheoryState/FaultState, please see detInsInc.
************************************************************************************************************************/
% if the sub-optimal pruning is not applied, return the input.
vitalityOpt(StatesFaultsAll, TheoryStateOut):-
    spec(heuris(H)),
    member(noOpt, H),
    findall([FNum, (TheoryState, FaultState)],
            (member((N1, N2, TheoryState, FaultState), StatesFaultsAll),
             FNum is N1 +N2),
            TheoryStateTem),
    sort(TheoryStateTem, TheoryStateTem2),
    transposeF(TheoryStateTem2, [_, TheoryStateOut]),!.

vitalityOpt(StatesFaultsAll, VitOptStates):-
    %writeLog([nl, write_term_c('--------- Pruning the sub-optimals with Threshod: '), write_term_c(Theres), nl, finishLog]),
    findall([TotalScores, TheoryState1, FaultState1],
            (member((_, _, TheoryState1, FaultState1), StatesFaultsAll),
             TheoryState1 = [_,_, _, TheoryIn, _, _],
             vitality(FaultState1, TheoryIn, [], VitState, (0,0), TotalScores),
             writeLog([nl, write_term_c('The vitality of the repaired theory is :'), write_term_c(VitState), nl,
                       write_term_c(' Vitality TotalScores are: '), write_term_c(TotalScores), nl, finishLog])),    % The repaired theory is not strictly dominated by any others.
            VitalStates),
    sort(VitalStates, Sorted),
    last(Sorted, [MaxScore, _, _]),  % get the scores of the most vital axiom.
    findall((TheoryState1, FaultState1),
              member([MaxScore, TheoryState1, FaultState1], Sorted),
            VitOptStates).

/**********************************************************************************************************************
    mergeRs(RepStates, RepStatesNew, TheoryIn):- if the theory of two states are same, then merge these two states.
        Only the states where the theory is different with the original theory will be taken into account.
    Input:  RepStates is a list of theory state: [[Repairs, EC, EProof, TheoryNew, TrueSetE, FalseSetE],...]
            TheoryIn is the theory that has not been repaired in this round.
    Output: RepStatesNew is also a list of [[Repairs, EC, EProof, TheoryNew, TrueSetE, FalseSetE]...]
************************************************************************************************************************/
mergeRs(RepStates, RepStatesNew, TheoryIn):-
    mR(RepStates, [], RepStatesNew, TheoryIn).

mR([], SIn, SOut, TheoryIn):-
    findall(StateNew,
            (member([[Rs, BanRs], EC, EProof, TheoryRep, TrueSetE, FalseSetE],SIn),
             TheoryRep \= TheoryIn,
             minimal(TheoryRep, EC, Rs, MiniT, RsOut), % only take the minimal set of the theory into account.
             StateNew = [[RsOut, BanRs], EC, EProof, MiniT, TrueSetE, FalseSetE]),
        SOut).

% The theory state is already in SIn.
mR([H|Rest], SIn, Sout, TheoryIn):-
    H = [[Rs, _]|StateT],
    % the main body of the state occur in the later states, then it is a redundancy. maintain the one cost least w.r.t. the length of repairs.
    member([[Rs2,RsBan2]|StateT], SIn), !,
    length(Rs, L1),
    length(Rs2, L2),
    (L1< L2-> replace([[Rs2,RsBan2]|StateT], H, SIn, SNew),
        mR(Rest, SNew, Sout, TheoryIn), !;
     L1 >= L2-> mR(Rest, SIn, Sout, TheoryIn)).

% H is not in SIn yet, but the theory is not been repiared so ignore it and continue.
mR([H|Rest], SIn, Sout, TheoryIn):-
    H = [_, _, _, TheoryRep, _, _],
    TheoryRep = TheoryIn,
    mR(Rest, SIn, Sout, TheoryIn).

% H is not in SIn yet and the theory is repaired so add it as a novel state and continue.
mR([H|Rest], SIn, Sout, TheoryIn):-
    H = [_, _, _, TheoryRep, _, _],
    TheoryRep \= TheoryIn,
    mR(Rest, [H| SIn], Sout, TheoryIn).
