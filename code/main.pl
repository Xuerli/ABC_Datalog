/*
Date: 07 Jan 2019
Macintosh HD⁩/⁨Users⁩/lixue⁩/GoogleDrive⁩/01PHD⁩/01program⁩/eclipse-workspace⁩/ABC_Clean⁩/src⁩
*/

:- use_module(library(lists)).
:-[preprocess, concepChange, equalities, repairPlanGen, repairApply].
    % clear all assertions. So main has to be compiling before the input theory file.
:-    maplist(retractall, [trueSet(_), falseSet(_), heuristics(_), protect(_), spec(_)]).

/********************************************************************************************************************** Global Variable and their values.
debugMode:    0 -- no write_term information.
            1 -- write_term informaiton.
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
:-spy(pause).
pause.

abc:-
    % Initialisation
    supplyInput,
    % Initialision: the theory, the preferred structure, the signature, the protected items and Equality Class and Inequality Set.
    initTheory(Theory),    % clear previous data and initialise new ones.
    precheckPS,
    % setup log
    fileName('record', Fname),
    open(Fname, write, StreamRec),
    
    fileName('repNum', Fname2),
    open(Fname2, write, StreamRepNum),
    assert(spec(repNum(StreamRepNum))),
    
    (exists_file('repTimeHeu.txt')->
     open('repTimeHeu.txt', append, StreamRepTimeH);
    \+exists_file('repTimeHeu.txt')->
    open('repTimeHeu.txt', write, StreamRepTimeH)),
    assert(spec(repTimeH(StreamRepTimeH))),

    (exists_file('repTimenNoH.txt')->
     open('repTimenNoH.txt', append, StreamRepTimeNH);
    \+exists_file('repTimenNoH.txt')->
    open('repTimenNoH.txt', write, StreamRepTimeNH)),
    assert(spec(repTimeNH(StreamRepTimeNH))),
        
    maplist(assert, [spec(debugMode(1)), spec(logStream(StreamRec))]),
    %(OverloadedPred \= [] -> concepChange(OverloadedPred,  AllSents, RepSents, CCRepairs, Signature, RSignature);        %Detect if there is conceptual changes: a predicate has multiple arities.
    %RepSents = AllSents, CCRepairs = []),
    
    %statistics(walltime, [_ | [ExecutionTime1]]),
    statistics(walltime, [S,_]),%statistics(walltime, Result) sets Result as a list, with the head being the total time since the Prolog instance was started, and the tail being a single-element list representing the time since the last
    
    % writeLog([nl,write_term('--------------executation time 1---'), nl,write_term('time takes'),nl, write_term(ExecutionTime1),nl]),
    % repair process
    detRep(Theory, AllRepStates),
    writeLog([nl,write_term('--------------AllRepStates: '),write_termAll(AllRepStates),nl, finishLog]),

    % Sort and remove duplicate repairs.
    %quicksort(AllRepTheos, RepairsSorted),
    %eliminateDuplicates(RepairsSorted, SetOfRepairs),
    % output
    
    statistics(walltime, [E,_]),
    ExecutionTime is E-S,
    
    writeLog([nl,write_term('--------------executation time 2---'),
                nl,write_term('time takes'),nl, write_term(ExecutionTime),nl]),
    %ExecutionTime is ExecutionTime1 + ExecutionTime2,
    output(AllRepStates, ExecutionTime),
    close(StreamRec),
    close(StreamRepNum),
    close(StreamRepTimeNH),
    close(StreamRepTimeH),
    nl,write_term('-------------- Finish. --------------'),nl.

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
            
            InsufIncomp = (_,INSUFF,ICOM),
            length(INSUFF,InsuffNum),
            length(ICOM,IncompNum),
            assert(spec(faultsNum(InsuffNum, IncompNum))),
            
             (InsufIncomp = (_,[],[])->
                     TheoryRep = ([fault-free, 0, TheoryState]);    % if the theory is fault free.
             % Otherwise, repair all the faults and terminate with a fault-free theory or failure due to out of the costlimit.
              InsufIncomp \= (_,[],[])->
                      repInsInc(TheoryState, 0, InsufIncomp, TheoryRep))),
            AllRepTheos1), 
    % Only select the minimal repairs w.r.t. the number of repair plans.
    findall((Len, Rep), 
                (member(Rep, AllRepTheos1),
                 Rep = [_,_ ,[[RepPlans,_]|_]],
                 length(RepPlans, Len)),
            AllRepTheos2),
    sort(AllRepTheos2, [(MiniCost, _)|_]),
    setof(RepState, member((MiniCost, RepState), AllRepTheos2), AllRepSolutions).

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
    TheoryState = [_, EC, _, Theory, TrueSetE, FalseSetE],
    writeLog([nl, write_term('---------Start detInsInc, Input theory is:------'), nl,
    nl,write_term(Theory),nl,write_termAll(Theory),nl,finishLog]),
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

     writeLog([nl, write_term('---------SufGoals is------'), nl,write_term(Suffs),
     nl, write_term('---------InsufGoals is------'), nl,write_term(InSuffs), finishLog]),

    % detect the incompatibilities
      findall(UnwProof,
           (member([+[Pre| Args]], FalseSetE),
            % skip equalities/inequalities which have been tackled.
            notin(Pre, [\=, =]),
            Goal = [-[Pre| Args]],
            % get all of a proof of Goal
            slRL(Goal, Theory, EC, UnwProof, [], []),
            UnwProof \= []),    % Detected incompatibility based on refutation.
           InComps),             % Find all incompatibilities.

    writeLog([nl, write_term('---------InComps are------'),nl, write_termAll(InComps), finishLog]),
    % detect the inconsistencies due to the violation of constrains
    findall(UnwProof,
              (member(Constrain, Theory),        % get a constrain axiom from the theory.
               notin(+_, Constrain),
               slRL(Constrain, Theory, EC, UnwProof, [], []),
               UnwProof \= []),
          Violations),
      writeLog([nl, write_term('---------Violations are------'),nl, write_termAll(Violations), finishLog]),
    append(InComps, Violations, Unwanted),
    FaultState = (Suffs, InSuffs, Unwanted).
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
    writeLog([nl,write_term('******** A solution is reached. *******'),nl]), !,
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
    write_term('******** Cost Limit is reached. *******'),nl,
    writeLog([nl, write_term('******** Cost Limit is reached. *******'),nl,
        write_term('Cost is: '), write_term(Cost), write_term('; Round: '), write_term(N),
        write_term('---------The current faulty TheoryState is------'), nl,write_termAll(TheoryState),
    nl, write_term('---------The remaining inffuficiencies are------'), nl,write_termAll(Insuf),
    nl, write_term('---------The remaining incompatibilities are------'), nl,write_termAll(Incomp), finishLog]).


% repair theory
repInsInc(TheoryStateIn, Layer, FaultStateIn, TheoryRep):-
    spec(roundNum(R)),
    writeLog([nl, write_term('--------- Start repInsInc round: '), write_term(R),nl, finishLog]),
    FaultStateIn = (SuffsIn, InsuffsIn, IncompsIn),
    TheoryStateIn = [_,_, _, TheoryIn, _, _],
    
    /*
    % repair insufficiencies first and then incompatibilities.
    (InsuffsIn \= [] ->
        appEach(InsuffsIn, [repairPlan, TheoryStateIn, SuffsIn], RepPlans), !;    % detect the remaining faults in the current theory in TheoryState.
    InsuffsIn = [] -> 
        appEach(IncompsIn, [repairPlan, TheoryStateIn, SuffsIn], RepPlans)),
    */
    % member(Insuff, InsuffsIn),
    % repairPlan(Insuff, TheoryStateIn, SuffsIn, RepPlan1),
    appEach(InsuffsIn, [repairPlan, TheoryStateIn, SuffsIn], RepPlans1),
    appEach(IncompsIn, [repairPlan, TheoryStateIn, SuffsIn], RepPlans2),
    append(RepPlans1, RepPlans2, RepPlans),
    % RepPlans = [RepPlan1|RepPlans2],
    length(RepPlans, RepPlansLen),
    writeLog([nl, write_term(RepPlansLen),write_term(' fault\'s new repair plans found: '), write_term(RepPlans), nl,nl,nl,write_term(TheoryIn),nl, finishLog]),

    repCombine(RepPlans, TheoryIn, RepSolutions),
    
    appEach(RepSolutions, [appRepair, TheoryStateIn], RepStatesTem),
    %print('000000'),print(RepStatesTem),nl,nl,print('RepStatesTem'),nl,nl,        
    sort(RepStatesTem, RepStatesAll),
    length(RepStatesAll, LengthO),
    writeLog([nl, write_term('-- There are '), write_term(LengthO),
                  write_term(' repaired states: '),nl,write_termAll(RepStatesAll), nl, finishLog]),
    % prune the redundancy.
    mergeRs(RepStatesAll, RepStatesFine), 
    writeLog([nl, write_term('-- RepStatesFine '), write_term(RepStatesFine),nl, finishLog]),
    %print('111111 RepStatesFine'),print(RepStatesFine),nl,nl,            
    findall((FNum1, FNum2, RepState, FaultStateNew),
                    (member(RepState, RepStatesFine),
                      detInsInc(RepState, FaultStateNew),
                      FaultStateNew = (_, InSuffNew, InCompNew),
                      length(InSuffNew, FNum1),
                      length(InCompNew, FNum2)),
             AllRepStates),
    length(AllRepStates, Length),
    writeLog([nl, write_term('-- All faulty states: '), write_term(Length),nl,
                write_termAll(AllRepStates), finishLog]),

     % pruning the sub-optimal.
    pareOpt(AllRepStates, Optimals),
    length(Optimals, LO),
    %print(Optimals),nl,nl,print(LO),nl,nl, 
%(Optimals =[([[[expand([+[mother,vble(y),vble(z)],-[female,vble(y)],-[parent,vble(y),vble(z)]]),expand([+[parent,[f],[a]]])],[]],[[[a]],[[b]],[[c]],[[d]],[[f]],[[g]]],[],[[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[+[female,[b]]],[+[female,[d]]],[+[male,[a]]],[+[male,[c]]],[+[male,[f]]],[+[male,[g]]],[+[mother,vble(y),vble(z)],-[female,vble(y)],-[parent,vble(y),vble(z)]],[+[parent,[a],[b]]],[+[parent,[a],[c]]],[+[parent,[d],[b]]],[+[parent,[f],[a]]]],[[+[father,[a],[b]]],[+[father,[a],[c]]],[+[mother,[d],[b]]],[+[father,[f],[a]]]],[[+[mother,[a],[b]]],[+[mother,[a],[c]]],[+[father,[d],[b]]],[+[father,[g],[a]]],[+[father,[g],[c]]]]],[([-[father,[a],[b]]],[[([-[father,[a],[b]]],[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[[a]/vble(x),[b]/vble(y)],[-[male,[a]],-[parent,[a],[b]]],[0,0]),([-[male,[a]],-[parent,[a],[b]]],[+[male,[a]]],[],[-[parent,[a],[b]]],[0,0]),([-[parent,[a],[b]]],[+[parent,[a],[b]]],[],[],[0,0])]]),([-[father,[a],[c]]],[[([-[father,[a],[c]]],[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[[a]/vble(x),[c]/vble(y)],[-[male,[a]],-[parent,[a],[c]]],[0,0]),([-[male,[a]],-[parent,[a],[c]]],[+[male,[a]]],[],[-[parent,[a],[c]]],[0,0]),([-[parent,[a],[c]]],[+[parent,[a],[c]]],[],[],[0,0])]]),([-[mother,[d],[b]]],[[([-[mother,[d],[b]]],[+[mother,vble(y),vble(z)],-[female,vble(y)],-[parent,vble(y),vble(z)]],[[b]/vble(z),[d]/vble(y)],[-[female,[d]],-[parent,[d],[b]]],[0,0]),([-[female,[d]],-[parent,[d],[b]]],[+[female,[d]]],[],[-[parent,[d],[b]]],[0,0]),([-[parent,[d],[b]]],[+[parent,[d],[b]]],[],[],[0,0])]]),([-[father,[f],[a]]],[[([-[father,[f],[a]]],[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[[a]/vble(y),[f]/vble(x)],[-[male,[f]],-[parent,[f],[a]]],[0,0]),([-[male,[f]],-[parent,[f],[a]]],[+[male,[f]]],[],[-[parent,[f],[a]]],[0,0]),([-[parent,[f],[a]]],[+[parent,[f],[a]]],[],[],[0,0])]])],[],[]),([[[expand([+[mother,vble(y),vble(z)],-[female,vble(y)],-[parent,vble(y),vble(z)]]),expand([+[father,[f],[a]]])],[]],[[[a]],[[b]],[[c]],[[d]],[[f]],[[g]]],[],[[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[+[father,[f],[a]]],[+[female,[b]]],[+[female,[d]]],[+[male,[a]]],[+[male,[c]]],[+[male,[f]]],[+[male,[g]]],[+[mother,vble(y),vble(z)],-[female,vble(y)],-[parent,vble(y),vble(z)]],[+[parent,[a],[b]]],[+[parent,[a],[c]]],[+[parent,[d],[b]]]],[[+[father,[a],[b]]],[+[father,[a],[c]]],[+[mother,[d],[b]]],[+[father,[f],[a]]]],[[+[mother,[a],[b]]],[+[mother,[a],[c]]],[+[father,[d],[b]]],[+[father,[g],[a]]],[+[father,[g],[c]]]]],[([-[father,[a],[b]]],[[([-[father,[a],[b]]],[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[[a]/vble(x),[b]/vble(y)],[-[male,[a]],-[parent,[a],[b]]],[0,0]),([-[male,[a]],-[parent,[a],[b]]],[+[male,[a]]],[],[-[parent,[a],[b]]],[0,0]),([-[parent,[a],[b]]],[+[parent,[a],[b]]],[],[],[0,0])]]),([-[father,[a],[c]]],[[([-[father,[a],[c]]],[+[father,vble(x),vble(y)],-[male,vble(x)],-[parent,vble(x),vble(y)]],[[a]/vble(x),[c]/vble(y)],[-[male,[a]],-[parent,[a],[c]]],[0,0]),([-[male,[a]],-[parent,[a],[c]]],[+[male,[a]]],[],[-[parent,[a],[c]]],[0,0]),([-[parent,[a],[c]]],[+[parent,[a],[c]]],[],[],[0,0])]]),([-[mother,[d],[b]]],[[([-[mother,[d],[b]]],[+[mother,vble(y),vble(z)],-[female,vble(y)],-[parent,vble(y),vble(z)]],[[b]/vble(z),[d]/vble(y)],[-[female,[d]],-[parent,[d],[b]]],[0,0]),([-[female,[d]],-[parent,[d],[b]]],[+[female,[d]]],[],[-[parent,[d],[b]]],[0,0]),([-[parent,[d],[b]]],[+[parent,[d],[b]]],[],[],[0,0])]]),([-[father,[f],[a]]],[[([-[father,[f],[a]]],[+[father,[f],[a]]],[],[],[0,0])]])],[],[])],    pause;true),
    writeLog([    nl, write_term('--The number of Optimals: '), write_term(LO), nl, write_termAll(Optimals), finishLog]),
    % get one optimal repaired theory along with its remaining faults and applied repairs Rep.
    member((TheoryStateOp, FaultStateOp), Optimals),
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
    %writeLog([nl, write_term('--------- Pruning the sub-optimals with Threshod: '), write_term(Theres), nl, finishLog]),
    findall((TheoryState1, FaultState1),
            (member((NumF11, NumF12, TheoryState1, FaultState1), StatesFaultsAll),
             TheoryState1 = [[Rs1, _]|_],
             length(Rs1, NumR1),
             Cost1 is NumR1 + NumF11 + NumF12,
             forall((member((NumF21, NumF22, TheoryState2, _), StatesFaultsAll),
                      TheoryState2 = [[Rs2, _]|_],
                     length(Rs2, NumR2),
                     Cost2 is NumR2 + NumF21 + NumF22),
                    (%writeLog([nl, write_term('Cost1 & Cost2 is ---------'),nl,write_term(Cost1), write_term(Cost2), finishLog]),
                      Cost2 >= Cost1))),    % The repaired theory is not strictly dominated by any others.
            OptStates).

% domination if f11*<f21 and f12 *< f22        
pareOptBak(StatesFaultsAll, OptStates):-
    writeLog([nl, write_term('--------- start pruning the sub-optimals ---------'),nl, finishLog]),
    findall((TheoryState, FaultState),
            (member((NumF11, NumF12, TheoryState, FaultState), StatesFaultsAll),
             forall(member((NumF21, NumF22, _, _), StatesFaultsAll),
                     \+strDominated([NumF21, NumF22], [NumF11, NumF12]))),    % The repaired theory is not strictly dominated by any others.
            OptStates).


/**********************************************************************************************************************
    mergeRs(RepStates, RepStatesNew):- if the theory of two states are same, then merge these two states.
    Input:  RepStates is a list of theory state: [[Repairs, EC, EProof, TheoryNew, TrueSetE, FalseSetE],...]
    Output: RepStatesNew is also a list of [[Repairs, EC, EProof, TheoryNew, TrueSetE, FalseSetE]...]
************************************************************************************************************************/
mergeRs(RepStates, RepStatesNew):-
    mR(RepStates, [], RepStatesNew).

mR([], SIn, SOut):-
    findall(StateNew,
            (member([[Rs, BanRs], EC, EProof, TheoryIn, TrueSetE, FalseSetE],SIn),
             minimal(TheoryIn, EC, Rs, MiniT, RsOut), % only take the minimal set of the theory into account.
             StateNew = [[RsOut, BanRs], EC, EProof, MiniT, TrueSetE, FalseSetE]),
        SOut).

% The theory state is already in SIn.
mR([H|Rest], SIn, Sout):-
    H = [[Rs, _]|StateT],
    % the main body of the state occur in the later states, then it is a redundancy. maintain the one cost least w.r.t. the length of repairs.
    member([[Rs2,RsBan2]|StateT], SIn), !,
    length(Rs, L1),
    length(Rs2, L2),
    (L1< L2-> replace([[Rs2,RsBan2]|StateT], H, SIn, SNew),
        mR(Rest, SNew, Sout), !;
     L1 >= L2-> mR(Rest, SIn, Sout)).

% H is not in SIn yet
mR([H|Rest], SIn, Sout):-
    mR(Rest, [H| SIn], Sout).
    