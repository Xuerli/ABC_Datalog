
/*********************************************************************************************************************************
    weakenVble, mergePlan,
            reformation relevant.
**********************************************************************************************************************************/

% reformation repair plans generated based on a pair of unified arguments
weakenVble(TargCl, Suffs,  VCP, TheoryIn, RepPlan):-
    spec(heuris(Heuristics)),
    notEss2suff(Suffs, TargCl), !,    % TODO: or being sufficient by having the variable being bound with one constant
    (
    %CR3 wekaen variable to constant.
    notin(noVabWeaken, Heuristics),
    member((V1, OrigCons), VCP),
    % Heuristic1: check that there must be more than one argument in the target rule. Otherwise, the rule would contain no variables after weaken one to a constant.
    setof(vble(V),
                ((member(+[_|Args], TargCl); member(-[_|Args], TargCl)),
                member(vble(V), Args)),
            [_|[_|_]]),
    % generate the constant
    dummyTerm(OrigCons, TheoryIn, NewCons),
    RepPlan = weaken(V1, NewCons, TargCl)). 

% the input clause is essential, then can apply if there is a unique essential const.
weakenVble(TargCl, Suffs, VCP, _, RepPlan):-
    spec(heuris(Heuristics)),
    notin(noVabWeaken, Heuristics),
    essSubs(Suffs, TargCl, SubstList),
    member((V1, _), VCP),
    % if the variable is bound to one constant in the proofs of the sufficiency where the input clause is essential.
    setof(C,    (member(Subst, SubstList),
                subst(Subst, V1, C)),
        [CSuff]), %Bound to only 1 particular constant
        
    % then the variable can be weaken to that constant so it won't introduce insufficiency.
    RepPlan = weaken(V1, CSuff, TargCl).

/**********************************************************************************************************************
   mergePlan(Mismatches, [PG| ArgsG], TargetLit, TargCl, TheoryIn, RepPlan, TargCls)
        Generate a repair plan of merge predicate
   Input:    Mismatches: the mismatched predicate and/or arguments between the goal argument and the target argument
            TargetLit: the target literal whose predicate and/or argument will be merged as the goal's
            TargCl: the clause where TargetLit comes
            TheoryIn: the object theory
   Output:     RepPlan: a repair plan of merge predicate
               TargCls: all the clauses that contains the predicate to be merged.
************************************************************************************************************************/
mergePlan(Mismatches, [PG| ArgsG], TargetLit, TargCl, TheoryIn, RepPlan, TargCls):-
    Mismatches = (predicate, ArgDiff),
    spec(protList(ProtectedList)),
    flatten(ProtectedList, ProtectedListF),
    % Get the predicate in the targeted literal
    prop(TargetLit, [PT| ArgsT]),
    length(ArgsT, ArityT),
    length(ArgsG, ArityG), 
    (intersection([PT, +[PT|_], -[PT|_]], ProtectedListF, [])-> %If it is not protecterd
        (ArityT > ArityG->
            % make PG's arity ArityT, and replace all PG with PR
            RepPlan = merge(PT, PG, ArgsG, dec);
        ArgDiff = []->
            % replace all PG with PR
            RepPlan = merge(PT, PG, ArgsG, equ);
        ArityT < ArityG->
            % increase PG's arity by adding ArgDiff and then replace all PG with PR
            RepPlan = merge(PT, PG, ArgDiff, inc)),
        findall(Cl, (member(Cl, TheoryIn), (member(+[PT|_], Cl);member(-[PT|_], Cl))), TargCls);
    
    
    % When PG is under protected, only refom the literal not all accurance of PG,
    % if that Literal is not the only occurance of PG.
    intersection([PT, +[PT|_], -[PT|_]], ProtectedListF, Int), Int =[_|_]->
     termOcc(PT, TheoryIn, Occurance),
     Occurance > 1,         % reform that literal won't make PG gone.
     (ArityT > ArityG->
            % make PG's arity Arity, and rename the PG with PR
            RepPlan = rename(PT, PG, ArgsG, TargetLit, TargCl, dec);
      ArgDiff = []->
            % replace all PG with PR
            RepPlan = rename(PT, PG, ArgsG, TargetLit, TargCl, equ);
      ArityT < ArityG->
            % increase PG's arity by adding ArgDiff and then rename the PG with PT
            RepPlan = rename(PT, PG, ArgDiff, TargetLit, TargCl, inc)),
    TargCls = [TargCl]).

% Only rename the instance of the mismatched predicate in the target clause.
renamePred(Mismatches, [PG| _], TargetLit, TargCl, RepPlan, [TargCl]):-
    Mismatches = (predicate, []),
    appLiteral(TargetLit, [replacePos, 1, 0, PG], LitNew),
    appLiteral(TargetLit, [nth0, 1, 0], PT),
    replace(TargetLit, LitNew, TargCl, ClNew),
    RepPlan = rename(PT, PG, TargCl, ClNew).

% generate reformation repair plan when the predicate is matched but arguments.
renameArgs(Mismatches, Nth, Evi, SuffGoals, MisNum, TheoryIn, RepPlan, TargCls):-
    Mismatches = [_|_],
    spec(protList(ProtectedList)),
    writeLog([nl,write_term_c('--renameArgs: Mismatches:'),nl,write_term_c(Mismatches),nl,
      write_term_c(ProtectedList),nl,finishLog]),
    %   print('@@@@@@'),nl,print(Mismatches),nl,print(ProtectedList),nl,print('@@@@@@@'),nl,

    findall([(COrig, CTarget, C1Cl), C1Cl],
                (member((C1, C2),Mismatches),
                nth0(Nth, [C1, C2], COrig),    % Get the original constant as COrig. (C1 when Nth=0, C2 otherwise)
                delete([C1, C2], COrig, [CTarget]),    % Get the other constant as CTarget.
                COrig = [CC],
                notin(CC, ProtectedList),
                traceBackC(COrig, Evi, C1Cl),
                % occur(+_, C1Cl),
                member(C1Cl, TheoryIn),    % it is an axiom from the theory not the preferred structure.
                notin(C1Cl, ProtectedList),
                asserProCheck(C1Cl, ProtectedList),
                notEss2suff(SuffGoals, C1Cl)),
                RS),
    sort(RS,RSS),
    length(RSS, MisNum),     % have found the clause of all mismached pairs
    transposeF(RSS, [MisPairs, TargCls]),
    
    RepPlan = rename(MisPairs),
    writeLog([nl,write_term_c('--renameArgs: RepPlanS:'),nl,write_term_c(RepPlan),nl,
        nl,write_term_c('--renameArgs: TargCls:'),nl,write_term_c(TargCls),nl, finishLog]).

% generate reformation repair plan of extend a constant to a variable when the predicate is matched but arguments.
extCons2Vble(Mismatches, Nth, Evi, MisNum, OrgCl, TheoryIn, RepPlan, TargCls):-
    Mismatches = [_|_],
    spec(protList(ProtectedList)),
    %((Mismatches =  [([load3], [load1])]; Mismatches =  [([load1], [load3])])->pause;true),
    findall([(COrig, NewVble, C1Cl), C1Cl],
                (member((C1, C2),Mismatches),
                nth0(Nth, [C1, C2], COrig),    % Get the target constant.
                notin(COrig, ProtectedList),
                (traceBackC(COrig, Evi, C1Cl);C1Cl = OrgCl),
                member(C1Cl, TheoryIn),    % it is an axiom from the theory not the preferred structure.
                notin(C1Cl, ProtectedList),
                    % get the list of variables in the input clause.
                findall(X,
                        ( (member(+[_| Arg], C1Cl);
                           member(-[_| Arg], C1Cl)),
                          member(vble(X), Arg)),
                        AvoidList),
                getNewVble([COrig], AvoidList, [(COrig, NewVble)], _)),
                RS),
    sort(RS,RSS),
    length(RSS, MisNum),     % have found the clause of all mismached pairs
    transposeF(RSS, [MisPairs, TargCls]),
    RepPlan = extC2V(MisPairs),
    writeLog([nl,write_term_c('--extC2V: RepPlanS:'),nl,write_term_c(RepPlan),nl,
        nl,write_term_c('--extC2V: TargCls:'),nl,write_term_c(TargCls),nl, finishLog]).


/*********************************************************************************************************************************
    reformUnblock(UnresSubGoals, EC, Evi, SuffGoals, Theory,  Output):
            unblock a proof by reformation
    Input:  UnresSubGoals: a list of unresolvable subgoals.
            EC: the equivalence classes.
            Evi: the evidence of the proof to unblock
            ClUsed: the input clauses that constitute Evi
            Theory: the theory.
            SubsSuff: a list of wanted substitution lists, e.g., [[[a]/vble(x),[a]/vble(y)], [[b]/vble(x),[c]/vble(y)]]
    Output: The list of repair information: [[RepPlans, ClS], [RepPlans2, ClS2], ....]
               where [RepPlans, ClS] = [ass2rule(Axiom, NewRule),...]
               All repair plans in the list need to be applied to unblock a proof.
            ClS: the list of clauses to change by applying RepPlans.
**********************************************************************************************************************************/
reformUnblock([], _, _, _, _, []).
reformUnblock([H|T], Evi, ClUsed, SuffGoals, TheoryState, [HOut| RestOut]):-
        refUnblock(H, Evi, ClUsed, SuffGoals, TheoryState, HOut),
        reformUnblock(T, Evi, ClUsed, SuffGoals, TheoryState, RestOut).

refUnblock(-[PG| ArgsG],  Evi, ClUsed, SuffGoals, TheoryState, [RepPlan, TargCls]):- %TODO add positive literal
    TheoryState = [[_, RsBanned],EC, _, TheoryIn, _, _],
    % Get the original negative literal and its clause where -GTarg comes from.
    traceBackPos(-[PG| ArgsG], Evi,TheoryIn, InpLi, InpCl2, _),    % InpCl2 = [] if it comes from the preferred structure.
    spec(protList(ProtectedList)),
    writeLog([nl,write_term_c('Reformation: targeted evidence'),nl,write_term_c([PG| ArgsG]), finishLog]),
    % print('***'),nl,write_term_c('Reformation: targeted evidence'),nl,write_term_c([PG| ArgsG]),nl,
    %Choosing a clause to change here

    setof( (Axiom, [+[PT|ArgsT]], Mismatches, MisNum, MisPairPos,EviTemp),
            (member(Axiom, TheoryIn),
             \+member(Axiom, ClUsed),    % the clause that has been used in the proof should not be a candidate to change for resolving the remaining sub-goal, otherwise, the evidence will be broken.
             %occur(-_, Rule), % it is possible to merge an assertion's predicate with the goal's predicate
            %  retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
            slRL(Axiom, TheoryIn, EC, _, EviTemp, []), %TODO bug here
             (member((_,_,_,Theorem,_),EviTemp);member((Theorem,_,_,_,_),EviTemp)),
             Theorem = [+[PT| ArgsT]],
            % member(+[PT|ArgsT],Axiom), %Can this work? Simply  choose one
             % heuristics:  the rule whose head predicate is same with the goal predicate;
             % or only choose the rule whose arguments overlaps goal's arguments.
             (PT = PG->    argsMis(ArgsG, ArgsT, Mismatches, MisPairPos), % Find all mismatches and store in the variable. TODO: check 
                         length(Mismatches, MisNum);
             PT \= PG-> diff(ArgsG, ArgsT, ArgDiff),     
                        Mismatches = (predicate, ArgDiff),
                        length(ArgDiff, MisNum),
                        MisPairPos = [])),
            Cand),
    writeLog([nl,write_term_c('--------Reformation Candidates------'),nl, write_term_c(Cand), finishLog]),
    member((Axiom, [+[PT|ArgsT]], Mismatches, MisNum, MisPairPos,ProofRest), Cand),
    writeLog([nl,write_term_c('---------------Axiom is 1  '),write_term_c(Axiom), finishLog]),
    writeLog([nl,write_term_c('---------------Mismatches is 1  '),write_term_c(Mismatches), finishLog]),
    % nl,nl,nl,print('***'),nl,print(Axiom),nl,print(PT),nl,print(Mismatches),nl,print(MisNum),nl,print(MisPairPos),nl,print('***'),nl,
    % print('---'),nl,print(PG),nl,print(ArgsG),nl,print(InpCl2),nl,print('---'),nl,
    spec(heuris(Heuristics)),
    (% if the irresolvable sub-goal is not from the preferred structure, reform the sub-goal
        % Or if the Axiom is not under protected, reform it

        %Reform the axiom (not the goal)
        (notin(noRename, Heuristics), notin(Axiom, ProtectedList),
            % Axiom = [+Head|_],    %Change +Head to +[PT|ArgsT] to make sure the correct term is changed.
            (mergePlan(Mismatches, [PG| ArgsG], +[PT|ArgsT], Axiom, TheoryIn, RepPlan, TargCls); %SR1: merge both pred and args
            renamePred(Mismatches, [PG| ArgsG], +[PT|ArgsT], Axiom, RepPlan, TargCls); %OR
            renameArgs(Mismatches, 1, ProofRest, SuffGoals, MisNum, TheoryIn, RepPlan, TargCls);
            extCons2Vble(Mismatches, 1, Evi,MisNum,Axiom, TheoryIn, RepPlan, TargCls) %Just added... any problems?
            )); %PRoofrest is deleted

        (InpCl2 \= [], notin(InpCl2, ProtectedList),
                (% generate repair plan of merge(PP, PT, ArgDiff, inc) or rename(PP, PT, ArityT, TargetLit, TargCl, dec/inc).
                notin(noRename, Heuristics),
                (mergePlan(Mismatches, [PT|ArgsT], InpLi, InpCl2, TheoryIn, RepPlan, TargCls);
                renamePred(Mismatches, [PT|ArgsT], InpLi, InpCl2, RepPlan, TargCls);
                renameArgs(Mismatches, 0, Evi, SuffGoals, MisNum, TheoryIn, RepPlan, TargCls));
                extCons2Vble(Mismatches, 0, Evi,MisNum,InpCl2, TheoryIn, RepPlan, TargCls))); % SR2~

        % if both irresolvable sub-goal and Axiom are not under protected, try to generate repair plan of decrease the arity of PG.
        (   notin(noArityChange, Heuristics),
            Mismatches = [_|_], InpCl2 \= [], notin(InpCl2, ProtectedList), notin(Axiom, ProtectedList),
            % print('----newcheck----'),nl,print(InpCl2),nl,print(Axiom),nl,print(Mismatches),nl,print('------'),nl,
            % do not decrease the arity of a predicate if its arity is 1.
            length(ArgsG, ArityG), ArityG > 1,
            % If both input clauses are not under protected, neither the arity of their predicate.
            notin(arity(PG), ProtectedList), notin(prop(PG), ProtectedList) ->
            % There is no axiom containing PG is under protected.
            forall(member(Axiom, ProtectedList), (notin(+[PG|_], Axiom), notin(-[PG|_], Axiom))),
            % check that the arity of PG is larger than 1
            findall(Pos, nth1(Pos, MisPairPos, [_|_]), PosMis),
            % check if the argument is under protected
            forall(member(ArgDele, PosMis), notin(deleArg(PG, ArgDele), RsBanned)),
            findall(Cl, (member(Cl, TheoryIn),
                        (member(+[PG|_], Cl); member(-[PG|_], Cl))),
                        TargCls),

            % Then decrease the arity of PG by deleting the arguments on the mismatched positions.
            RepPlan = arityDec(PG, TargCls, PosMis))).


refUnblock(+[PG| ArgsG],  Evi, ClUsed, SuffGoals, TheoryState, [RepPlan, TargCls]):- %TODO add positive literal
    TheoryState = [[_, RsBanned],EC, _, TheoryIn, _, _],
    % Get the original negative literal and its clause where -GTarg comes from.
    traceBackPos(+[PG| ArgsG], Evi,TheoryIn, InpLi, InpCl2, _),    % InpCl2 = [] if it comes from the preferred structure.
    spec(protList(ProtectedList)),
    writeLog([nl,write_term_c('Reformation: targeted evidence'),nl,write_term_c([PG| ArgsG]), finishLog]),
    % print('***'),nl,write_term_c('Reformation: targeted evidence'),nl,write_term_c([PG| ArgsG]),nl,
    %Choosing a clause to change here

    setof( (Axiom, [-[PT|ArgsT]], Mismatches, MisNum, MisPairPos,EviTemp),
            (member(Axiom, TheoryIn),
             \+member(Axiom, ClUsed),    % the clause that has been used in the proof should not be a candidate to change for resolving the remaining sub-goal, otherwise, the evidence will be broken.
             %occur(-_, Rule), % it is possible to merge an assertion's predicate with the goal's predicate
            %  retractall(spec(proofNum(_))), assert(spec(proofNum(0))),
            slRL(Axiom, TheoryIn, EC, _, EviTemp, []), %TODO bug here
             (member((_,_,_,Theorem,_),EviTemp);member((Theorem,_,_,_,_),EviTemp)),
             Theorem = [-[PT| ArgsT]],
            % member(+[PT|ArgsT],Axiom), %Can this work? Simply  choose one
             % heuristics:  the rule whose head predicate is same with the goal predicate;
             % or only choose the rule whose arguments overlaps goal's arguments.
             (PT = PG->    argsMis(ArgsG, ArgsT, Mismatches, MisPairPos), % Find all mismatches and store in the variable. TODO: check 
                         length(Mismatches, MisNum);
             PT \= PG-> diff(ArgsG, ArgsT, ArgDiff),     
                        Mismatches = (predicate, ArgDiff),
                        length(ArgDiff, MisNum),
                        MisPairPos = [])),
            Cand),
    writeLog([nl,write_term_c('--------Reformation Candidates------'),nl, write_term_c(Cand), finishLog]),
    member((Axiom, [-[PT|ArgsT]], Mismatches, MisNum, MisPairPos,ProofRest), Cand),
    writeLog([nl,write_term_c('---------------Axiom is 1  '),write_term_c(Axiom), finishLog]),
    writeLog([nl,write_term_c('---------------Mismatches is 1  '),write_term_c(Mismatches), finishLog]),
    spec(heuris(Heuristics)),
    (% if the irresolvable sub-goal is not from the preferred structure, reform the sub-goal
        % Or if the Axiom is not under protected, reform it

        %Reform the axiom (not the goal)
        (notin(noRename, Heuristics), notin(Axiom, ProtectedList),
            % Axiom = [+Head|_],    %Change +Head to +[PT|ArgsT] to make sure the correct term is changed.
            (mergePlan(Mismatches, [PG| ArgsG], -[PT|ArgsT], Axiom, TheoryIn, RepPlan, TargCls); %SR1: merge both pred and args
            renamePred(Mismatches, [PG| ArgsG], -[PT|ArgsT], Axiom, RepPlan, TargCls); %OR
            renameArgs(Mismatches, 1, ProofRest, SuffGoals, MisNum, TheoryIn, RepPlan, TargCls);
            extCons2Vble(Mismatches, 1, Evi,MisNum,Axiom, TheoryIn, RepPlan, TargCls) %Just added... any problems?
            )); %PRoofrest is deleted

        (InpCl2 \= [], notin(InpCl2, ProtectedList),
                (% generate repair plan of merge(PP, PT, ArgDiff, inc) or rename(PP, PT, ArityT, TargetLit, TargCl, dec/inc).
                notin(noRename, Heuristics),
                (mergePlan(Mismatches, [PT|ArgsT], InpLi, InpCl2, TheoryIn, RepPlan, TargCls);
                renamePred(Mismatches, [PT|ArgsT], InpLi, InpCl2, RepPlan, TargCls);
                renameArgs(Mismatches, 0, Evi, SuffGoals, MisNum, TheoryIn, RepPlan, TargCls));
                extCons2Vble(Mismatches, 0, Evi,MisNum,InpCl2, TheoryIn, RepPlan, TargCls))); % SR2~

        % if both irresolvable sub-goal and Axiom are not under protected, try to generate repair plan of decrease the arity of PG.
        (   notin(noArityChange, Heuristics),
            Mismatches = [_|_], InpCl2 \= [], notin(InpCl2, ProtectedList), notin(Axiom, ProtectedList),
            
            % do not decrease the arity of a predicate if its arity is 1.
            length(ArgsG, ArityG), ArityG > 1,
            % If both input clauses are not under protected, neither the arity of their predicate.
            notin(arity(PG), ProtectedList), notin(prop(PG), ProtectedList) ->
            % There is no axiom containing PG is under protected.
            forall(member(Axiom, ProtectedList), (notin(+[PG|_], Axiom), notin(-[PG|_], Axiom))),
            % check that the arity of PG is larger than 1
            findall(Pos, nth1(Pos, MisPairPos, [_|_]), PosMis),
            % check if the argument is under protected
            forall(member(ArgDele, PosMis), notin(deleArg(PG, ArgDele), RsBanned)),
            findall(Cl, (member(Cl, TheoryIn),
                        (member(+[PG|_], Cl); member(-[PG|_], Cl))),
                        TargCls),

            % Then decrease the arity of PG by deleting the arguments on the mismatched positions.
            RepPlan = arityDec(PG, TargCls, PosMis))).