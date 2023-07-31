:-[ruleMod, reformation, util].

%% No goal.
repairPlan(Goal, TheoryState, _, TheoryState):-
    occur(Goal, [(_, []), [], ([],_)]), !.

% TODO: MERGE insufficiencies goals with same predicate and then add the rule which proves all of them

%Build a proof of insufficiency
repairPlan((Goal, Evidences), TheoryState, Suffs, RepPlansOut):-
    write_term_c('------repair plan 1 for insuff--------'),nl,write_term_All(Goal),nl,write_term_All(Suffs),nl,
    TheoryState = [[RsList, RsBanned], _, _, _, _, _], !,

    spec(heuris(Heuristics)),
    ( delete(Heuristics, noOpt, [])->    % No heuristics
        spec(repTimeNH(RunTimeFile)), !;
    delete(Heuristics, noOpt, [_|_])->    % Has heuristics
        spec(repTimeH(RunTimeFile))),
    statistics(walltime, [S1,_]),
    findall(RepairInfo, %TODO ok until this.
                (buildP((Goal, Evidences), TheoryState, Suffs, RepairInfo),
                RepairInfo = [insuff, (RepPlans, _), _],
                RepPlans \= [],
                % check if the repair plan conflicts previous ones or it has been suggested
                intersection(RepPlans, RsBanned, []),
                intersection(RepPlans, RsList, [])),
            RepPlansTem),
    sort(RepPlansTem, RepPlansOut),
    %print('RepPlansOut:'),nl, write_term_All(RepPlansOut),nl,
    statistics(walltime, [E1,_]),

    SFRTime is E1-S1,
    write(RunTimeFile, SFRTime), write(RunTimeFile, '; Insuff:'),
    write(RunTimeFile, (Goal, Evidences)), write(RunTimeFile, ';'),
    write(RunTimeFile, TheoryState),write(RunTimeFile, ';'),
    write(RunTimeFile, RepPlansOut),
    nl(RunTimeFile),

    length(RepPlansOut, N),
    nl,write_term_c(N), nl, write_term_c('repair plans  for buildP:'),write_term_c([Goal, Evidences]),
    nl,nl,nl,write_term_All(RepPlansOut),nl,
    halt,
    writeLog([nl,write_term_c(N), write_term_c('repair plans  for buildP:'),write_term_c([Goal, Evidences]),
            nl,nl,nl,write_term_All(RepPlansOut),nl, finishLog]).

%Block a proof of incompatability
repairPlan(ProofInp, TheoryState, Suffs, RepPlansOut):-
    ProofInp = [_|_],
    TheoryState = [[RsList, RsBanned], _, _, _, _, _], !,
    spec(heuris(Heuristics)),
    ( delete(Heuristics, noOpt, [])->    % No heuristics
        spec(repTimeNH(RunTimeFile)), !;
    delete(Heuristics, noOpt, [_|_])->    % Has heuristics
        spec(repTimeH(RunTimeFile))),

    statistics(walltime, [S1,_]),
    findall(RepairInfo,
                (blockP(ProofInp, TheoryState, Suffs, RepairInfo),
                RepairInfo = [incomp, (RepPlans, _), _],
                RepPlans \= [],
                % check if the repair plan conflicts previous ones or it has been suggested
                intersection(RepPlans, RsBanned, []),
                intersection(RepPlans, RsList, [])),
            RepPlansTem),
    sort(RepPlansTem, RepPlansOut),
    statistics(walltime, [E1,_]),
    SFRTime is E1-S1,
    write(RunTimeFile, SFRTime), write(RunTimeFile, '; Incomp: '),
    write(RunTimeFile,ProofInp), write(RunTimeFile, ';'),
    write(RunTimeFile, TheoryState),write(RunTimeFile, ';'),
    write(RunTimeFile, RepPlansOut),
    nl(RunTimeFile),

    length(RepPlansOut, N),
    nl,write_term_c(N),write_term_c(' repair plans for blockP:'),write_term_c(ProofInp), nl,nl,nl,write_term_All(RepPlansOut),nl,halt,
    writeLog([nl,write_term_c(N),write_term_c(' repair plans for blockP:'),write_term_c(ProofInp), nl,nl,nl,write_term_All(RepPlansOut),nl, finishLog]).


/**********************************************************************************************************************
    blockProof(Proof, TheoryState, SuffGoals, [RepPlan, TargetCls]): block one unwanted proof.
                The reason of not blocking all unwanted proofs is that the theory is changed and the other unwanted proofs could be changed.
    Input:  Proof: unwanted proof of an incompatibility.
            TheoryState: [[RsIn, RsBanned], EC, EProof, TheoryIn, TrueSetE, FalseSetE], for more information, please see unaeMain.
                RsIn: a list of repairs that have been applied to get TheoryIn, each of which is in the format of (Rs, Cl, I)
                RsBanned: the repairs that have been banned to apply, e.g., the ones failed in applying or violates some constrains.
    Output: [RepPlan]: a list of the repair plans which block Proof.
            TargetCls:    the clauses on which the RepPlan will apply.
            ClP: a collection of the clauses which constitute the proof.
************************************************************************************************************************/
%% Block the unwanted proof by adding a unprovable precondition. CR5,CR6
blockP(Proof, TheoryState, SuffGoals, [incomp, ([RepPlan], ClT), ClS]):-
    spec(heuris(Heuristics)),
    % not all four heuristics are employed.
    deleteAll([noRuleChange, noPrecAdd, noAss2Rule, noAxiomDele], Heuristics, [_|_]),
    writeLog([nl, write_term_c('-------- Start blockProof1: -------- '),
            nl, write_term_All(Proof), finishLog]),
    TheoryState = [_, EC, _, TheoryIn, TrueSetE, FalseSetE],
    writeLog([nl, write_term_c('TheoryIn is: '), write_term_c(TheoryIn),nl,nl,write_term_All(TheoryIn), finishLog]),

    % get the clauses in the unwanted proof.
    findall([Cl, Subs],
                    (member((_, Cl, Subs, _, _), Proof),
                    is_list(Cl)),
            CandRules),
    transposeF(CandRules, [ClS, _]),
    member([AxiomOrg, IncomSubs], CandRules),    % target at one clause,
    traceBackClause(AxiomOrg,Proof,TheoryIn,Axiom),
    writeLog([nl, write_term_c('Original Axiom is: '), write_term_c(Axiom),nl, finishLog]),
    spec(protList(ProtectedList)),
    notin(Axiom, ProtectedList),

    % CR6
    (Axiom\=[+[_|_]], intersection([noRuleChange, noPrecAdd], Heuristics, []),    % if it is a rule
        % Add a irresolvable precondition to the rule to make it unprovable.
        % Appliable when the new rule still works for the sufficiency of which the old rule is essential)
        getAdjCond(Axiom, IncomSubs, SuffGoals, TheoryIn, EC, TrueSetE, FalseSetE, RepCands),
        % get single repair plan, RepPlan is an atom not a list.
        member(RepPlan, RepCands);

    
    Axiom=[+[Pred|_]], intersection([noRuleChange, noAss2Rule], Heuristics, []), notin(asst(Pred), ProtectedList),
        % Turn the assertion to a rule to make it unprovable.
        % Appliable when it is not essential for any sufficiency)
        % RepPlan = [(ass2rule(Axiom, NewRule), Axiom),...]
        asser2rule(Axiom, EC, SuffGoals, TheoryIn, TrueSetE, FalseSetE, RepCands),
        member(RepPlan, RepCands);

    % CR5: delete the axiom.
    notin(noAxiomDele, Heuristics),  notEss2suff(SuffGoals, Axiom), notin(Axiom, ProtectedList),
        (Axiom\=[+[_|_]]; Axiom=[+[Pred|_]], notin(asst(Pred), ProtectedList)),
        % if the axiom is not essential to an sufficiency, it can be deleted.
        RepPlan = delete(Axiom)),
    ClT = [Axiom].

%TODO add similar thing here which for CR8 which introduces the positive literal that is unprovable. 

%% Block the unwanted proof by reformation (CR1,CR2,CR3,CR4) %TODO: consider functions and functions + CR7
blockP(Proof, TheoryState, SuffGoals, [incomp, ([RepPlan], [TargCl]), ClS]):-
    spec(heuris(Heuristics)),
    notin(noReform, Heuristics),
    spec(protList(ProtectedList0)),
    TheoryState = [_, _, _, TheoryIn, TrueSetE, FalseSetE],
    append(TrueSetE, FalseSetE, PrefStruc),
    append(ProtectedList0, PrefStruc, ProtectedList),


    findall(Cl, (member((_, Cl, _, _, _), Proof), is_list(Cl)), ClS),
    writeLog([nl, write_term_c('-------- Start blockProof2: reformation -------- '),
            nl, write_term_c('-------- Proof is:'),nl,write_term_c(Proof), nl,nl,
            nl, write_term_c('-------- SuffGoals is:'),nl,write_term_c(SuffGoals), nl,nl, finishLog]),

    %print(' Proof is ' ), nl,print(Proof),nl,
    member(TrgResStep, Proof),
    %print(' TrgResStep is ' ), nl,print(TrgResStep),nl,
    TrgResStep = ([PropGoal|_], InpCl1, _, _, _), %PropGoal is signed.
    split(Proof, TrgResStep, ResStepPre, _),    % split the proof at TrgResStep.
    prop(PropGoal,[P|_]), %P is the predicate to be resolved.

    % InpCl1 = [+[P| ArgsCl1]| _],        % automatically skip RS based on unae, as their InputClause =unae.
    traceBackClause(InpCl1,ResStepPre,TheoryIn,RInpCl1),
    %Obtain args of the relevant goal in RInpCl1
    (member(+[P|ArgsCl1], RInpCl1), isOpSign(+[P|ArgsCl1],PropGoal),InpClLit = +[P|ArgsCl1]; member(-[P|ArgsCl1], RInpCl1), isOpSign(-[P|ArgsCl1],PropGoal),InpClLit = -[P|ArgsCl1]),

    traceBackPos(PropGoal, ResStepPre, TheoryIn, OrgLit, RInpCl2, _),    % Get the original negative literal and its clause where -GTarg comes from.
    prop(OrgLit, [P|ArgsG]),

    % not both clauses are under protected.
    (notin(-_, RInpCl1)-> deleteAll([asst(P), RInpCl2], ProtectedList, [_|_]);
     member(-_, RInpCl1)-> deleteAll([RInpCl1, RInpCl2], ProtectedList, [_|_])),

    %Check correct unification (to make sure this is the resolved clause)
    unification([P|ArgsG],[P|ArgsCl1],[],[],_,_,[]),
   
    % get all candidates of unifiable pairs to block.
    %TODO: add new pairs that consider variable and functions, functions and constants, functions and functions etc. 
    %Unification is successful, remember!
    
    findall([CC, VCG, VCIn, VV,VFunc],
                (   nth0(X, ArgsCl1, C1),
                    nth0(X, ArgsG, C2),
                    (% if C1 and C2 are two constants
                     is_cons(C1), C1 = C2, CC = C1, VCG = [], VCIn = [], VV= [], VFunc = [];

                     % if C1 is a variable and C2 is a constant / function
                     C1 = vble(_),
                     is_cons_or_func(C2), VCIn = (C1, C2), CC = [], VCG = [], VV= [], VFunc = [];

                     % if C2 is a variable and C1 is a constant
                     is_cons_or_func(C1),
                     C2 = vble(_),    % If the variable occurs in the head of InpCl2, omit it.
                     % InpCl2 = [+[_| ArgsHead2]|_],
                     % because the repair plan of weakening it COULD be generated when targeting  RS0 where InpCl2 is the input clause. But if RS0 is between variables then no repair plan will be generated by it
                     % notin(vble(Y), ArgsHead2),
                     VCG = (C2, C1), CC = [], VCIn = [], VV= [], VFunc = [];

                     % if C1 and C2 are two vables
                     C1 = vble(_),
                     C2 = vble(_),
                     VV = [C1,C2], CC=[], VCG=[], VCIn= [], VFunc = [];

                     % both C1 and C2 are functions
                    is_func(C1), is_func(C2),
                    unification(C1,C2,[],[],_,_,[]),
                    VFunc = [C1, C2], CC=[], VCG=[], VCIn= [], VV= []
                     )),
            UPairs),
    sort(UPairs, SortedPairs),    % the pairs are not empty
    SortedPairs = [_|_],

    transposeF(SortedPairs, [CCP, VCPG, VCPIn, VV,VFunc]),
    %print(' [CCP, VCPG, VCPIn] is ' ), nl,print([CCP, VCPG, VCPIn]),nl,
    %Repair strategies that target InpCl1 (which is the right side of unification, the input clause)
    (    (notin(RInpCl1, ProtectedList),
            TargLit = InpClLit,
            TargCl = RInpCl1,
            
            (
            % CR4: increase arguemnt
            notin([arity(P)], ProtectedList), %notEss2suff(SuffGoals, TargCl),
             RepPlan = arityInc(P, TargLit, TargCl,OrgLit, RInpCl2); %

            % CR1: rename predicate
            notin(noRename,Heuristics),
            notin(P,ProtectedList),
            notEss2suff(SuffGoals,TargCl),
            dummyTerm(P,TheoryIn,NewP),
            RepPlan = renamePred(P,NewP,TargLit,TargCl);

            % CR2: renaming a constant
            notin(noRename, Heuristics),
            notEss2suff(SuffGoals, TargCl), 
            findall(C, member((_, C), VCPG), CS),    % if the variable is from the goal literal and the constant is from InpCl1
            append(CS, CCP, ConsIn),    % get all the constants contained by InpCl1 which contribute to the unification.
            member(C, ConsIn),
            RepPlan = rename(C, TargLit, TargCl); 

            % CR3: weaken variable to a constant
            weakenVble(TargCl, SuffGoals, VCPIn, TheoryIn, RepPlan)));

    % Repair strategies that target InpCl2
        (notin(RInpCl2, ProtectedList), RInpCl2 \= [],    % InpCl2 is neither an input clause under protected, nor from the preferred structure.
             TargLit = OrgLit,
            TargCl = RInpCl2,
            
            (
            % CR1: rename predicate
            notin(noRename,Heuristics),
            notin(P,ProtectedList),
            notEss2suff(SuffGoals,TargCl),
            dummyTerm(P,TheoryIn,NewP),
            RepPlan = renamePred(P,NewP,TargLit,TargCl);

            % CR2: renaming a constant
            notin(noRename, Heuristics),
            notEss2suff(SuffGoals, TargCl), 
            findall(C, member((_, C), VCPIn), CS),    % if the variable is from the goal literal and the constant is from InpCl1
            append(CS, CCP, ConsIn),    % get all the constants contained by InpCl1 which contribute to the unification.
            member(C, ConsIn),
            RepPlan = rename(C, TargLit, TargCl); 

            %CR3: weaken variable to a constant    
            weakenVble(TargCl, SuffGoals, VCPG, TheoryIn, RepPlan);

            % CR4: arityInc
             % if 1. there are at least one more occurrence of the predicate in an assertion, which avoid mirror repaired theories.
            findall([+[P|ArgsTem]], %Heuristic 1, P.74
                  (member([+[P|ArgsTem]], TheoryIn),
                   notin([+[P|ArgsTem]], [RInpCl1, RInpCl2])),
                      [_|_]),
             % and if 2.P is not under protected,
             notin([arity(P)], ProtectedList),
             % then the goal literal could be the unique one.
             RepPlan = arityInc(P, TargLit, TargCl, InpClLit, RInpCl1))) 
             ),


    %nl,nl,print(' RepPlan is '), nl, print(RepPlan),nl,nl,
    writeLog([nl, write_term_c('--Blocking Repair Plan11 InpClause:'),
                nl, write_term_c(TargCl),nl, nl,
                write_term_c(RepPlan),nl, finishLog]).

/**********************************************************************************************************************
   buildProof(Evidences, TheoryState, Suffs, Output):
        Generate a repair to unblock a proof of Goal and try best to avoid introducing insufficiecy.
   Input:    TheoryState = [[RsIn, RsBanned],EC, EProof, TheoryIn, TrueSetE, FalseSetE], for more information, please see unaeMain.
               Evidences: [Goal, Evis], where
                   Goal(-Assertion): the negative literal that cannot be resolved away by TheoryIn.
                   Evidences: the partial proofs of Goal.
               Suffs: all provable goals with their proofs.
   Output:     RepairPlans = a list of repair plans for unblocking an evidence of the goal.
               TargCls: a list of clauses to which the repair plan will apply.
               ClE: a collection of the remaining unprovabe sub-goals in all the evidences of that Goal.
************************************************************************************************************************/
%Nothing to build it it is empty.
buildP([], _, _, _):-fail,!.
buildP(([], []), _, _, _):-fail,!.

buildP((Goal, Evidences), TheoryState, SuffGoals, [insuff, (RepPlans, TargCls), ClS]):-
    spec(heuris(Heuristics)),
    writeLog([nl,write_term_c('--------Start unblocking 1 based on evidences  ------'),nl, finishLog]),
    Goal \= [],
    TheoryState = [_,EC, _, TheoryIn, _, _],
    % Get one partial proof Evi and its clauses information lists ClsList.
    member(Evi, Evidences), %This is the whole proof until something cannot be proved

    findall((Num, GoalsRem, ProofCur),
               ((member((Subgoals, _, _, _, _), Evi); member((_, _, _, Subgoals, _), Evi)),
               retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
                findall([SubG, Proof],
                            (member(SubG, Subgoals),
                            slRL([SubG], TheoryIn, EC, Proof,_,[]),
                            Proof = [_|_]),        % found a non-empty proof
                        ResovlableG),
                transposeF(ResovlableG, [ResGs, SubGProofs]),    % get all resolvable sub-goals
                subtract(Subgoals, ResGs, GoalsRem),
                length(GoalsRem, Num),
                appAll(append, SubGProofs,[Evi], ProofCur,1)),    % ProofCur is a set of RS ignoring their order that results the remaining irresolvalble sub-goals only.
           Rems),
    sort(Rems, SortedRems), %Each entry is one of the RS, with all the subgoals that failed.
    SortedRems = [(MiniRemG, _,_)|_],        % get the number of the least unresolvable subgoals
    member((MiniRemG, Unresolvables, ProofCur), SortedRems),    % get one minimal group of the unresovable sub-goals.
    writeLog([nl,write_term_c('-- Unresolvables and ProofCur is :'),nl,write_term_c(Unresolvables),nl,write_term_c(ProofCur),nl,  finishLog]),
    write_term_c('---Unresolvables and proofcur----'),nl,
    write_term_c(Unresolvables),nl,
    write_term_c(ProofCur),nl,
    write_term_c('---end unresolvables----'),nl, 

    (notin(noPrecDele, Heuristics),    % unblocking by deleting unprovable preconditions: SR5 (done and verified.)
        writeLog([nl,write_term_c('--Deleting unprovable preconditions:'),nl,write_term_c(Unresolvables),nl,  finishLog]),
        delPreCond(Unresolvables, Evi,TheoryIn, RepPlans1, TargCls),
        RepPlans = [RepPlans1];

    notin(noReform, Heuristics),    % by reformation. (SR1, SR2)
        writeLog([nl,write_term_c('--Reformation: Unresolvables:'),nl,write_term_c(Unresolvables),nl,  finishLog]),
        findall(Cl, member((_,Cl,_,_,_), Evi), ClUsed), %TODO up till here
        reformUnblock(Unresolvables, Evi, ClUsed, SuffGoals, TheoryState,  RepInfo),
        transposeF(RepInfo, [RepPlans, TargClsList]),
        setof(Cl, (member(List, TargClsList),
                    member(Cl, List)),
              TargCls);

    intersection([noAxiomAdd, noAssAdd], Heuristics, []),    % by adding the goal as an axiom or a rule which derives the goal. (SR3, SR4)
        setof([expand([SProp]),    [SProp]],
                    (member(PropG, Unresolvables),
                    prop(PropG,PPropG),
                    replace(vble(_), [dummy_vble_1], PPropG, Prop),
                    addOpSign(PropG,Prop,SProp)
                    ),
                RepPairs),
        transposeF(RepPairs, [RepPlans, TargCls])),

    % get all of the clauses which constitute the target proof to unblock
    findall(Cl, (member((_,Cl,_,_,_), ProofCur), is_list(Cl)), ClE1),
    append(TargCls, ClE1, ClS1),
    delete(ClS1, [], ClS),

    writeLog([nl,write_term_c('--Unblocking 1: RepPlanS:'),nl,write_term_c(RepPlans),nl, write_term_All(TargCls),nl, finishLog]).



%% Repair the insufficiency by adding a rule whose head is the goal. == SR4
buildP((Goal, _), TheoryState, _, [insuff, (RepPlans, RuleNew), ClS]):-
    %% Repair the insufficiency by abduction.
    spec(heuris(Heuris)),
    notin(noAxiomAdd, Heuris),
    notin(noRuleChange, Heuris),
    writeLog([nl,write_term_c('--------Start unblocking 2 by adding a rule ------'),nl,finishLog]),
    TheoryState = [_,EC, _, TheoryIn, TrueSetE, FalseSetE],
    Goal = [-PropG|_],

    % get all relevant theorems to the goal
    findall((L, Theorem),
                (PropG = [_ |Args],
                 member(C, Args),
                 allConstraintsC(TheoryIn, EC, C, Theorems), %
                 member(Theorem, Theorems),
                 Theorem = [+[_|Arg2]],
                 deleteAll(Args, Arg2, DistArg),
                 length(DistArg, L)),    % L is the number of arguments in Goal but not in the theorem.
                RelTheorems),
    mergeTailSort(RelTheorems, [(_, Cands)|_]), % get all candidates which is the most relevant theorems to Goal.
    deleteAll(Cands, FalseSetE, Cands2),    % the precondition does not correspond to the false set.

    % Heuristic7: When there is other theorems of C, do not consider the inequalities of C.
    (member([+[P|_]], Cands2), P \= (\=)-> delete(Cands2, [+[\=|_]],Cands3);
     Cands3 = Cands2),

    % get all restrict constrains which are under protected.
    findall(Constrain,(member(Constrain, TheoryIn),
                     notin(+_, Constrain),
                     spec(protList(ProtectedList)),
                     member(Constrain, ProtectedList)),
            ResCons),
    % find all violations of the candidate rule CandRule w.r.t. protected constains in the thoery.
    findall([+Prop],
                (member([+Prop], Cands3),
                 member(Constrain, ResCons),    % check based on a protected constrain axiom.
                 % there is a proof of the violation of the constrain.
                 retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
                 slRL(Constrain, [[+Prop], [+PropG]], EC, [_|_], [], []),
                 writeLog([nl,write_term_c('**** Constrains check failed: '),nl,
                     write_term_c([+PropG, -Prop]),
                    write_term_c(' vs '),write_term_c(Constrain),nl])),    % proof exists
            VioCand),
    deleteAll(Cands3, VioCand, RuleCands),

    % Heuristic8:    When searching for a precondition, either add all theorems as preconditions or add one of them.
    (member([+Prop], RuleCands), generalise([+PropG, -Prop], RuleTem);    % formalise the rule which derive the goal.
    setof(-Prop, member([+Prop], RuleCands), AllPred),
    generalise([+PropG| AllPred], RuleTem)),

    % check incompatibilities.
    findall(Proof,
             (member([+[Pre| Args]], FalseSetE),
              % skip equalities/inequalities which have been tackled.
              notin(Pre, [\=, =]),
              NVioSent = [-[Pre| Args]],
              % get all of a proof of Goal
              retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
              slRL(NVioSent, [RuleTem| TheoryIn], EC, Proof, [], []),
              Proof \= []),                                       % Detect incompatibility based on refutation.
         Incompat),                                      % Find all incompatibilities. FaultsProofs is the proofs that the objective theory proves one or more violative sentences.
  (Incompat = []-> BigPlan = [([expand(RuleTem)], RuleTem)];
  Incompat = [_|_]->
      % check if there is an incompatibility caused by RuleR6
      findall(Subs,
              (member(IncompProof, Incompat),
               member((_,RuleTem,Subs,_,_), IncompProof)),
              IncomSubsRaw),

      sort(IncomSubsRaw, IncomSubs),
      % if the new rule is not involved in any inconsistencies, then no adjustment precondition is needed.
      (IncomSubs = []->BigPlan = [([expand(RuleTem)], RuleTem)];
      IncomSubs = [_|_]->
            retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
              findall(Proof,
                          (slRL(Goal, [RuleTem| TheoryIn], EC, Proof, [], []),
                          Proof \=[]),
                      Proofs),

              getAdjCond(RuleTem, IncomSubs, [(Goal, Proofs)], [RuleTem| TheoryIn], EC, TrueSetE, FalseSetE, CandAll),
              (findall(([expand(RuleTem2)], RuleTem2),
                      (member(add_pre(Precondition, _), CandAll),
                       sort([Precondition| RuleTem], RuleTem2)),
                       BigPlan);
              CandAll = []-> BigPlan = [([expand(RuleTem)], RuleTem)]))),

    member((RepPlans, RuleNew), BigPlan),
    % get all of the clauses which constitute the target proof to unblock
    retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
    findall(Cl, (slRL(Goal, [RuleNew|TheoryIn], EC, ProofUnblocked, [], []),
                member((_,Cl,_,_,_), ProofUnblocked),
                is_list(Cl)),     % do not record keyword 'unae'
            ClS),
   writeLog([nl,write_term_c('--Unblocking 2: RepPlanS/CLE'),nl,write_term_c(RepPlans),nl,write_term_All(ClS),nl, finishLog]).


%% Repair the insufficiency by adding a rule whose head is the goal. REVERSE + and -. == SR4
buildP((Goal, _), TheoryState, _, [insuff, (RepPlans, RuleNew), ClS]):-
    %% Repair the insufficiency by abduction.
    spec(heuris(Heuris)),
    notin(noAxiomAdd, Heuris),
    notin(noRuleChange, Heuris),
    writeLog([nl,write_term_c('--------Start unblocking 2 by adding a rule ------'),nl,finishLog]),
    TheoryState = [_,EC, _, TheoryIn, TrueSetE, FalseSetE],
    Goal = [+PropG|_],

    % get all relevant theorems to the goal
    findall((L, Theorem),
                (PropG = [_ |Args],
                 member(C, Args),
                 allConstraintsC(TheoryIn, EC, C, Theorems), %
                 member(Theorem, Theorems),
                 Theorem = [-[_|Arg2]],
                 deleteAll(Args, Arg2, DistArg),
                 length(DistArg, L)),    % L is the number of arguments in Goal but not in the theorem.
                RelTheorems),
    mergeTailSort(RelTheorems, [(_, Cands)|_]), % get all candidates which is the most relevant theorems to Goal.
    deleteAll(Cands, FalseSetE, Cands2),    % the precondition does not correspond to the false set.

    % Heuristic7: When there is other theorems of C, do not consider the inequalities of C.
    (member([-[P|_]], Cands2), P \= (\=)-> delete(Cands2, [-[\=|_]],Cands3);
     Cands3 = Cands2),

    % get all restrict theorems which are under protected.
    findall(Constrain,(member(Constrain, TheoryIn),
                     notin(-_, Constrain),
                     spec(protList(ProtectedList)),
                     member(Constrain, ProtectedList)),
            ResCons),
    % find all violations of the candidate rule CandRule w.r.t. protected constains in the thoery.
    findall([-Prop],
                (member([-Prop], Cands3),
                 member(Constrain, ResCons),    % check based on a protected constrain axiom.
                 % there is a proof of the violation of the constrain.
                 retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
                 slRL(Constrain, [[-Prop], [-PropG]], EC, [_|_], [], []),
                 writeLog([nl,write_term_c('**** Constrains check failed: '),nl,
                     write_term_c([-PropG, +Prop]),
                    write_term_c(' vs '),write_term_c(Constrain),nl])),    % proof exists
            VioCand),
    deleteAll(Cands3, VioCand, RuleCands),

    % Heuristic8:    When searching for a precondition, either add all theorems as preconditions or add one of them.
    (member([-Prop], RuleCands), generalise([-PropG, +Prop], RuleTem);    % formalise the rule which derive the goal.
    setof(+Prop, member([-Prop], RuleCands), AllPred),
    generalise([-PropG| AllPred], RuleTem)),

    % check incompatibilities.
    findall(Proof,
             (member([-[Pre| Args]], FalseSetE),
              % skip equalities/inequalities which have been tackled.
              notin(Pre, [\=, =]),
              NVioSent = [+[Pre| Args]],
              % get all of a proof of Goal
              retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
              slRL(NVioSent, [RuleTem| TheoryIn], EC, Proof, [], []),
              Proof \= []),                                       % Detect incompatibility based on refutation.
         Incompat),                                      % Find all incompatibilities. FaultsProofs is the proofs that the objective theory proves one or more violative sentences.
  (Incompat = []-> BigPlan = [([expand(RuleTem)], RuleTem)];
  Incompat = [_|_]->
      % check if there is an incompatibility caused by RuleR6
      findall(Subs,
              (member(IncompProof, Incompat),
               member((_,RuleTem,Subs,_,_), IncompProof)),
              IncomSubsRaw),

      sort(IncomSubsRaw, IncomSubs),
      % if the new rule is not involved in any inconsistencies, then no adjustment precondition is needed.
      (IncomSubs = []->BigPlan = [([expand(RuleTem)], RuleTem)];
      IncomSubs = [_|_]->
            retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
              findall(Proof,
                          (slRL(Goal, [RuleTem| TheoryIn], EC, Proof, [], []),
                          Proof \=[]),
                      Proofs),

              getAdjCond(RuleTem, IncomSubs, [(Goal, Proofs)], [RuleTem| TheoryIn], EC, TrueSetE, FalseSetE, CandAll),
              (findall(([expand(RuleTem2)], RuleTem2),
                      (member(add_pre(Precondition, _), CandAll),
                       sort([Precondition| RuleTem], RuleTem2)),
                       BigPlan);
              CandAll = []-> BigPlan = [([expand(RuleTem)], RuleTem)]))),

    member((RepPlans, RuleNew), BigPlan),
    % get all of the clauses which constitute the target proof to unblock
    retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
    findall(Cl, (slRL(Goal, [RuleNew|TheoryIn], EC, ProofUnblocked, [], []),
                member((_,Cl,_,_,_), ProofUnblocked),
                is_list(Cl)),     % do not record keyword 'unae'
            ClS),
   writeLog([nl,write_term_c('--Unblocking 2: RepPlanS/CLE'),nl,write_term_c(RepPlans),nl,write_term_All(ClS),nl, finishLog]).


%% Repair the insufficiency by analogising an existing rule and give them different preconditions. SR4 again
buildP((Goal, Evidences), TheoryState, Suffs, [insuff, (RepPlans, RuleR7), ClS]):-
    spec(heuris(Heuristics)),
    notin(noRuleChange, Heuristics),
    notin(noAnalogy, Heuristics),
    spec(protList(ProtectedList)),
    writeLog([nl,write_term_c('--------Start unblocking 3: by Analogical Abduction for ------'),
              nl,  write_term_c(Goal),nl, finishLog]),
    TheoryState = [_,EC, _, TheoryIn, TrueSetE, FalseSetE],
    findall(Rule,
            (member((_, Proofs), Suffs),
             member(Proof, Proofs),
             member((_,Rule,_,_, _), Proof),    % Sub is the substitutions that have applied to the rule in Proof.
             is_list(Rule),                        % do not take the keyword 'unae' into account.
             notin(Rule, ProtectedList),
             length(Rule, L),
             L>1),
            RulesUseful),
     (RulesUseful = []->
         writeLog([nl, write_term_c('******** No rules are useful, Analogy fails.'),nl, finishLog]);
         RulesUseful = [_|_]),

     findall(GoalRem,
               (member(Evi, Evidences),
                (member((Subgoals, _, _, _, _), Evi); member((_, _, _, Subgoals, _), Evi)),
                retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
                findall(SubG,
                            (member(SubG, Subgoals),
                            slRL([SubG], TheoryIn, EC, Proof,_,[]),
                            Proof = [_|_]),        % found a non-empty proof
                        ResovlableGs),    % get all resolvable sub-goals
                subtract(Subgoals, ResovlableGs, GoalRem),
                length(GoalRem, 1)),
           SingleGs),
    sort([Goal| SingleGs], SingleGoalList),        % get the list of the single unresolvable subgoal.
    writeLog([nl,write_term_c('-- The single unresolvable subgoal. is :'),nl,write_term_c(SingleGoalList),nl,  finishLog]),

    setof(Relevancy,
            (member(RuleC, RulesUseful),        % get a rule candidate
             member(TargetG, SingleGoalList),    % get a target goal candidate
             relevancy(RuleC, TargetG, TheoryIn, EC, Relevancy)), %Later: may change relevancy
         Relevancies), %TODO up till here

    % get the most relevant rule w.r.t. the goal.
    last(Relevancies, (S1, S2, RuleSR, TGoal, PreCondRel, PPs)),
       findall(-P, (member(-P, RuleSR), notin(-P, PreCondRel)), PSIrrela),
    writeLog([nl, write_term_c('The scored relevant rule is '), nl, write_term_c(RuleSR), nl,
            write_term_c(S1), write_term_c(','), write_term_c(S2), nl, finishLog]),

    % remove irrelevant preconditions
    deleteAll(RuleSR, PSIrrela, RuleR),
    RuleR \= [],
    TGoal = [-[PG| ArgG]],
    member(+[_|ArgsHR1], RuleR),
    delete(RuleR, +[_|ArgsHR1], Body1),

    % instantiate RuleR based on the target goal.
    unification([PG| ArgG], [PG| ArgsHR1], [],[],_, Substitution, []),        % If successful resolution
    subst(Substitution, Body1, Body2),
    % get the partner precondition which can be resolved by a theorem,
    % and the mis-matched arguemnts between the preconditions in Body2 and their partner preconditions.
    findall([PartPre, MisPairs],
            (member(-Precond, Body2),
             mmMatches(-Precond, PPs, PartPre, MisPairs)),
            Body3Info),

    % divid the list of the minimal argument mismatches MMPs
    transposeF(Body3Info, [Body4, MMPsList]),
    RuleR4 = [+[PG| ArgG]| Body4],
    % reorganise all mismatches as one list of constants.
    findall(C, (member(MMPs, MMPsList),
                member((C1,C2),MMPs),
                member(C, [C1,C2])), MMPsAll),

    % get the introduction preconditions for MMPs.
    getIntro(MMPsAll, EC, TheoryIn, IntroPs),
    writeLog([nl, write_term_c('The introduction preconditions are '), nl,
                write_term_All(IntroPs), nl, finishLog]),
    append(RuleR4, IntroPs, RuleR5),

    % generalisation
    generalise(RuleR5, RuleR6, _, _),    % e.g., Subs65 is [[a]/vble(z)]
    writeLog([nl, write_term_c('The generalised rule RuleR6 is'), nl,
                write_term_c(RuleR6), nl, finishLog]),

    % check incompatibilities.
      findall(Proof,
               (member([+[Pre| Args]], FalseSetE),
                % skip equalities/inequalities which have been tackled.
                notin(Pre, [\=, =]),
                NVioSent = [-[Pre| Args]],
                % get all of a proof of Goal
                retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
                slRL(NVioSent, [RuleR6| TheoryIn], EC, Proof, [], []),
                Proof \= []),                                       % Detect incompatibility based on refutation.
           Incompat),                                      % Find all incompatibilities. FaultsProofs is the proofs that the objective theory proves one or more violative sentences.

    % check if there is an incompatibility caused by RuleR6
    findall(Subs,
            (member(IncompProof, Incompat),
             member((_,RuleR6,Subs,_,_), IncompProof)),
            R6IncomSubsRaw),

    sort(R6IncomSubsRaw, R6IncomSubs),
    retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
    findall(Proof,
                (slRL(Goal, [RuleR6| TheoryIn], EC, Proof, [], []),
                Proof \=[]),
            Proofs),

    getAdjCond(RuleR6, R6IncomSubs, [(Goal, Proofs)], [RuleR6| TheoryIn], EC, TrueSetE, FalseSetE, CandAll),
    (member(add_pre(Precondition, _), CandAll)-> sort([Precondition| RuleR6], RuleR7);
     CandAll = []-> RuleR7 = RuleR6),

   writeLog([nl, write_term_c('--------The incompatibilities of R6 include'),
                nl, write_term_All(R6IncomSubs), nl,
               nl, write_term_c('--------The resulted rules of analogise RuleSR include'),
               nl, write_term_All(RuleR7), finishLog]),

    %convertForm([RuleSR, RuleR7], [SRAxiom, RuleNew]),    % rever the internal format of rules back to axioms
    RepPlans = [analogy(RuleSR, RuleR7)],
    retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
    % get all of the clauses which constitute the target proof to unblock
    findall(Cl, (slRL(Goal, [RuleR7|TheoryIn], EC, ProofUnblocked, [], []),
                member((_,Cl,_,_,_), ProofUnblocked),
                is_list(Cl)),
            ClS).
