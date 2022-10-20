
:- [util, utilRevise].

%% All repair plans are attached with the original axiom which will be changed in that repair plan.

/*********************************************************************************************************************************
    asser2rule(Axiom, EC, SuffGoals, Theory, TrueSetE, FalseSetE,  Output):
            turn a n assertion to a rule
    Input:  Axiom: an assertion which is involved in an unwanted proof.
            EC: the equivalence classes.
            Theory: the theory.
            SubsSuff: a list of wanted substitution lists, e.g., [[[a]/vble(x),[a]/vble(y)], [[b]/vble(x),[c]/vble(y)]]
            IncomSubs:  the list of unwanted substitution lists
            * both WGoals and UnwGoals are provalbe due to Rule.
            TrueSetE, FalseSetE: the preferred structure.
    Output: RepCands = [ass2rule(Axiom, NewRule),...]
**********************************************************************************************************************************/
% based on the wanted substitutions, get the pairs of a variable and its instanted constants in wanted proofs.
asser2rule(Axiom, EC, SuffGoals, Theory, TrueSetE, FalseSetE, RepCands):-
    writeLog([nl, write_term('-------- start asser2rule to find unprovable precondition'), nl,
            write_term('-- IncomSub='), write_term(IncomSub),nl,
            nl, write_term('-- SuffGoals='), write_term(IncomSub),nl,
            nl, write_term('-- Theory='), write_term(Theory),nl,
            nl,nl, write_termAll(Theory),nl, finishLog]),
    Axiom = [+[PA|ArgA]], !,

    % check if the axiom is essential to an sufficiency, do not make it unprovable.
    notEss2suff(SuffGoals, Axiom),

    % Heuristic: only get one layer of theorem
    delete(Theory, Axiom, Theory2),
    allTheoremsP(Theory2, PA, EC, TS),    % get all theorems of the target predicate.
    delete(TS, Axiom, TCan),
    findall([+[PA|ArgTrue]], member([+[PA|ArgTrue]], TrueSetE), Tures),
    append(TCan, Tures, TCands),

    findall(AvoidPreds, (member(Constrain, Theory2),
                        notin(+_, Constrain),
                        occur(-[PA|_], Constrain),
                        member(-[AvoidPreds|_],Constrain)),
            AvoidPList),

    findall(-[PP|Arg2New],
                (% target at another individual which is also an instance of PA.
                 member(([+[_|Args]],_), TCands),
                 member(C2, Args),
                 notin(C2,ArgA),        % find the candidates of unprovable conditions based on C2
                 % findall all theorems of that individual
                 allTheoremsC(Theory2, EC, C2, TS2),
                 deleteAll(TS2, FalseSetE, TS3),    % do not use anything from the false set.
                 append(TS3, TrueSetE, TAll),    % combine the true set.
                 member(Clause, TAll),
                 Clause = [+[PP|Arg2]],
                 notin(PP, [PA|AvoidPList]),    % the predicate is not in the avoid list
                 nth0(Pos, Arg2, C2),
                 replacePos(Pos, Arg2, vble(x), Arg2New)),    % prune the ones does not contain C2.
        Preconditions),

    length(ArgA, ArityA), PosAMax is ArityA-1,
    findall(ass2rule(Axiom, NewRule),
                    (member(-Pre, Preconditions),
                     between(0, PosAMax, PosA),
                     replacePos(PosA, ArgA, vble(x), ArgANew),
                     NewRule = [+[PA| ArgANew], -Pre],
                     % check that the original axiom is not derivable any more.
                     append(TrueSetE, Theory2, TheoryRich),
                     findall(Theorem, slRL(NewRule, TheoryRich, EC, _,_,Theorem),NewT),
                     notin(Axiom, NewT)),
            RepCands).

/*********************************************************************************************************************************
    getAdjCond(Rule, IncomSubs, SuffGoals, Theory, EC, TrueSetE, FalseSetE,  RepPlanS):
        add the adjustment preconditions (relevant) to Rule for proving WGoals while not proving UnwGoals.
    Input:  Rule: a rule which has been instantiated based on the goal which resolves the head of this rule.
            SubsSuff: a list of wanted substitution lists, e.g., [[[a]/vble(x),[a]/vble(y)], [[b]/vble(x),[c]/vble(y)]]
            IncomSubs:  the list of unwanted substitution lists
            * both WGoals and UnwGoals are provalbe due to Rule.
            Theory: the theory.
            EC: equivalence classes.
            TrueSetE & FalseSetE: the preferred structure.
    Output: RepPlanS: [add_pre(HP, Rule),...], where Rule is the input rule.
**********************************************************************************************************************************/
getAdjCond(_, [], _, _, _, _, _, []).
getAdjCond(Rule, IncomSub, SuffGoals, Theory, EC, TrueSetE, FalseSetE, RepPlanS):-
    writeLog([nl, write_term('-------- getAdjCond for  Rule: '), write_term(Rule),nl, finishLog]),
    member(+[PR| ArgR], Rule),    
    % get the list of predicates which cannot be the predicate of the target precondition
    findall(AvoidPred,
                (AvoidPred = PR;
                member(-[AvoidPred|_], Rule);    % predicates already in Rule
                member(Constrain, Theory),
                notin(+_, Constrain),
                occur(-[PR|_], Constrain),        % Predicates occurs together with PR in a constrain axiom
                member(-[AvoidPred|_],Constrain)),
        AvoidPList),
    findall(Predicate, 
                (member(Clause, Theory), 
                Clause\= Rule,
                (member(-[Predicate| _], Clause);member(+[Predicate| _], Clause)),
                notin(Predicate, AvoidPList)),
        PreCandsRaw),
    sort(PreCandsRaw, PreCands),    % remove dupliates
    writeLog([nl, write_term(' PreCands are: '), write_term(PreCands),nl, finishLog]), 
    findall(RepPlan, 
                (member(Pred, PreCands),
                adjCond(Pred, Rule, IncomSub, SuffGoals, Theory, EC, TrueSetE, FalseSetE, RepPlan);
                setof(vble(X), member(vble(X),ArgR), HeadVbles),
                RepPlan = add_pre(-[dummyPred|HeadVbles], Rule),
                writeLog([nl, write_term(' Found unprovable precondition : '), write_term(RepPlan),nl, finishLog])),
            RepPlanSTem), 
    sort(RepPlanSTem, RepPlanS),    % remove duplicates
    (RepPlanS = []-> fail,
          writeLog([nl, write_term(' ERROR: Failed in finding unprovable preconditions.'), nl, finishLog]);
     RepPlanS = [_|_]->
    writeLog([nl, write_term(' All found unprovable preconditions: '), write_term(RepPlanS),nl, finishLog])).

% getAdjCond: adds unprovable precondition
% SuffGoals is the sufficient goals or the substitutions of Rule in one proof of an sufficiency.
adjCond(P, Rule, IncomSub, SuffGoals, Theory, EC, TrueSetE, FalseSetE, RepPlan):-
    writeLog([nl, write_term('-------- start to find unprovable precondition candidates based on: '),
                write_term(P),nl, finishLog]), 
    IncomSub \= [], % if there is no incompatibilities, no adjustment precondition is needed.
    findall([(vble(X), [C]), GoalRule],
            (member((GoalRule, SuffProofs), SuffGoals),    % heuristic: only consider the goal whose proofs all contain the rule.
             forall(member(Proof, SuffProofs),
                     member((_, Rule, _, _, _), Proof)),
             member(Proof, SuffProofs),
             member((_, Rule, Subs, _, _), Proof),
             member([C]/vble(X), Subs)),
            RuleSuff),
    % get substitution pairs and the goals that Rule is essential.
    transposeF(RuleSuff, [VbCons, GoalRs]),
    mergeTailSort(VbCons, VbConsSC),
    %writeLog([nl, write_term('VbCons: '), nl, write_term(VbCons),nl, finishLog]),

    % get all constant arguments of the rule in the unwanted proof.
    subst(IncomSub, Rule, InstRule),
    findall(Arg,
            ((member(+[_|Args], InstRule);member(-[_|Args], InstRule)),
             member(Arg, Args)),
            ArgsAllRaw),
    % ArgsAll are the instantiated arguments of the rule in the unwanted proof.
    sort(ArgsAllRaw, ArgsAll),    
    % writeLog([nl, write_term('ArgsAll: '), nl, write_term(ArgsAll),nl]),
    % get all of the theorems of the predicate P which can be derived without Rule and the ones from the true set.
    delete(Theory, Rule, Theory2),
    spec(signature(Sig, _)),
    
    (allTheoremsP(Theory2, P, EC, TP),
    findall(T,member((T,_),TP), TS);    % Get all theorems of P.
     P = (\=)->    % Get the inequalities of Cconstant
        findall(ArgD, (member((_,_,ArgsDomains), Sig), member(ArgD, ArgsDomains)),
            Categories),
        findall([+[\=, C2, C1]],
                (member(Cat, Categories),
                member(C1, Cat),
                member(C2, Cat),
                equalSub([\=, C1, C2], EC, [])),
                TS);
     P = (=)->    
         findall([+[=, C1, C2]],
            (mmeber(Euqalities, EC),
            member(C1, Euqalities),
            member(C2, Euqalities),
            C1 \= C2),
            TS)),
    
    % consider the Extras propositions in the true set that does not need rule to prove & the ones occur in preconditions of rules
    findall([+[P|Args]], 
                ( member([+[P|Args]], TrueSetE), notin([-[P|Args]], GoalRs);
                  member(Cl, Theory), member(-[P|Args], Cl)),
                Extras),
    append(TS, Extras, TSAll),
    writeLog([nl, write_term('Found TSAll for: '),    write_term(P),nl, write_term(TSAll),nl, finishLog]), 
    
    % get the domains of each argument of P baed on these theorems.
    findall(ArgsP, member([+[P|ArgsP]], TSAll), ArgThs),
    % get the category for each argument where contains both variables and constants.
    transposeF(ArgThs, ArgCat),    
    % get the argument domains which contains only constants.
    appEach(ArgCat, [delete,vble(_)], ArgDomains),
    %writeLog([nl, write_term('ArgDomains: '), nl, write_term(ArgDomains),nl, finishLog]),
    % collect the diffrences of these theorems w.r.t. ArgsAll
    findall((Dif, [P| ArgsV]),            % collect a theorem's difference score together with the proposition of that theorem.
            (setArgs(ArgDomains, VbConsSC, ArgsAll, IncomSub, ArgsV),    % get candidates of the arguments of the precondition
             writeLog([nl, write_term(' upArg ArgsV is '),nl,write_term(ArgsV),nl, finishLog]),
             member(vble(X), ArgsV),    % there is at least one variable in the argument candidate.
             Precondition = [+[P| ArgsV]],
             subst(IncomSub, Precondition, PT),
                 % PT is not a theorem or proposition in the true set of the preferred structure.
                (notin(PT, TS), notin(PT, TrueSetE);
                % or PT is a proposition in the false set.
                member(PT, FalseSetE)),
             PT = [+[P| ArgsC]],
             deleteAll(ArgsAll, ArgsC, ArgRest),
             length(ArgRest, Dif)),        % the difference score of the theorem w.r.t. ArgsAll
             Diff),
    (Diff = []->
        writeLog([nl, write_term('******** Warning: No adjustment precondition candidates found'),nl, finishLog]),
        fail;
     Diff = [_|_]->    writeLog([nl, write_term('-------- The adjustment precondition candidates:'),
                     nl, write_termAll(Diff), finishLog])),
    mergeTailSort(Diff, [(_,Cands)|_]),    % get one of the most relevant proposition.

    % the precondition with the most variables will be the head.
    sort(Cands, [HP|_]),
    RepPlan = add_pre(-HP, Rule).


/**********************************************************************************************************************
    delPreCond(Unresolvables, Evi, RepPlan, TargCls):
            generate repair plan of deleting the unprovable preconditions from a rule.
    Input:  Unresolvables: a minimal group of the unresovable sub-goals.
            Evi is a partial proof
    Output: RepPlan: the repair plan of deleting which precondition from a rule.
            ClOld: the rule whose precondition is deleted.
************************************************************************************************************************/
delPreCond(Unresolvables, Evi, RepPlan, ClsOld):-
    spec(protList(ProtectedList)),
    
     % Get the original clause information which introduces all the remaining Subgoals, where the last subgoal is the one irresolvable.
    setof([OrigCl, (OrigCl, ClNew)],
                (member(-UnG, Unresolvables),
                traceBackPos(UnG, Evi, OrigLi, OrigCl, _),    % Get the original negative literal and its clause where -GTarg comes from.
                notin(OrigCl, [[]|ProtectedList]),            % That input clause is not protected from being deleted.
                length(OrigCl, L),
                L>2,                                        % Do not delete the unique precondition.
                delete(OrigCl, OrigLi, ClNew),                % remove the precondition which introduces the unprovable subgoal.
                orphanVb(ClNew, [])),                        % The resulting clause should not have any orphan variable.    
            Pairs),
    transposeF(Pairs, [ClsOld, RulePairs]),
    % Generate the repair plan of deleting unprovale preconditions from ClOld.
    RepPlan = dele_pre(RulePairs),

    writeLog([nl,write_term('--------Finish generating repair plan of deleting the unprovable precondition------'),
                nl, write_term(RepPlan), finishLog]).


/**********************************************************************************************************************
    relevancy(Rule, Goal, TheoryIn, EC, (S1, S2, Rule, Ps, PPs)):-
    Input: Goal: a goal clause:  [-[Precondition, Arg1, Arg2,...]]
           Rule: is a rule clause:[+[HP, A1,..], -[BP, A2...], -[BP2, A3...]]
           TheoryIn the input theory.
    Output: S1, 1 if the head predicate of Rule is same with Goal's predicate, otherwise 0.
            S2, the number of relevant preconditions in Rule w.r.t Goal.
            Rule, attached the input rule in the output.
            Ps: the relevant preconditions in Rule.
            PPs: the partner theorem of each relevant precondition.
************************************************************************************************************************/
relevancy(Rule, [], _, _, (0, 0, Rule, [])):-!.
relevancy(Rule, Goal, TheoryIn, EC, (S1, S2, Rule, Goal, Ps, PPs)):-
    Goal = [-[P| Args]],
    member(+[HP|_], Rule),
    % calculate S1: the relevance of the head.
    (P = HP -> S1 = 1; S1 = 0),

    % calculate S2: the relevancy of the body, and the partner theorems of a relevant precondition.
    findall([-[P1| Arg1], [+[P1| Arg2]]],
            (member(-[P1| Arg1], Rule),                % get a precondition whose predicate is P1,
             allTheoremsP(TheoryIn, P1, EC, Theorems),    % get all theorems of the predicate P1,
             member(([+[P1| Arg2]], _), Theorems),    % get the partner theorem of the precondition.
             unification([P1|Arg1], [P1|Arg2], [],[],_,_, []),    % that theorem can instantiate the precondition
             intersection(Args, Arg2, I),
             I \= []),
            PsAll),
    transposeF(PsAll, [Ps1, PPs]),
    sort(Ps1, Ps),    % remove the duplicates
    length(Ps, S2).


/**********************************************************************************************************************
    mmMatches(Precondition, Theorems, Partner, MMPs):
            get the minimal argument mismatches between the precondition and a theorem which is closest to it
    Input:     Precondition: a precondition to resolve away.
               Theorems: the possible theorem partners of the precondition
               RuleIn: the input rule
    Output: MisPairs: pairs of the mismatched arguments, where [(mm, partner),...].
            Partner: the closest theorem to the precondition which has the same predicate and the most same arguments.
************************************************************************************************************************/
mmMatches([], _, [], []):-!.
mmMatches(_, [], [], []):-!.
mmMatches(-[Pred| Arg], Theorems, Partner, MisPairs):-
    % get the closest theorem and negate it to be a candidate of a precondition.
    findall((Num, -[Pred| Arg2], Mismatches),
            (member([+[Pred| Arg2]], Theorems),
             % find Mismatches: the list of mismatched arguments.
             argsMis(Arg, Arg2, Mismatches,_),
             length(Mismatches, Num)),    % the length of Rs is the number of the mismatched arguments.
            M),
    %writeLog([nl,nl,write_term('---------M are-------'),nl,write_term(M),nl,finishLog]),
    mergeTailSort(M, [(_,Candidates)|_]),    % sort according to the length of Rs, and then the first is the minimal matches
    member((Partner, MisPairs),Candidates).
    %writeLog([nl,nl,write_term('---------MisPairs are-------'),nl,write_term(MisPairs),nl, finishLog]).

/**********************************************************************************************************************
    getIntro(Cons, EC, TheoryIn, IntroPs)):-get the introduction preconditions for constants in Cons.
    Input: Cons: a list of constants.
           EC: the equivalence classes.
           TheoryIn: the input theory.
    Output: IntroPs: the introduction preconditions whose arguments contain all the constants in Cons.
************************************************************************************************************************/
getIntro([], _, _, []).
getIntro(Cons, EC, TheoryIn, [IntroPreCond| Rest]):-
    Cons = [C1| _],
    allTheoremsC(TheoryIn, EC, C1, Theorems),    % all theorems whose arguemnts contain C1

    % get the precondition which contains the most of the target constants.
    findall((Num, ConsRest, -[P|Args]),            % record a candidate of the precondition
            (member(Theorem, Theorems),
             Theorem = [+[P|Args]],
             deleteAll(Cons, Args, ConsRest),     % omit all contained constants
             length(ConsRest, Num)),
            NumTheos),
    sort(NumTheos, [(Min,_,_)|_]),        % get the least number of the constants not contained by a theorem.  
    member((Min, ConsRest, IntroPreCond), NumTheos),
    getIntro(ConsRest, EC, TheoryIn, Rest).

/**********************************************************************************************************************
    setArgs(ArgDom, VbConsSC, ArgsAllF, IncomSubs, ArgsIn, ArgsOut):
        get the argument of a precondition
    Input: ArgDom:
           VbConsSC:
           ArgsAllF: the instantiated arguments of the rule in the unwanted proof.
           IncomSubs:the substitutions of the rule in the unwanted proof.
           ArgsIn:
    Output: ArgsOut:
************************************************************************************************************************/
%upArgs([], _, _, _, _, [vble(x)]):- !.
setArgs(ArgDom, VbConsSC, ArgsAllF, IncomSubs, ArgsOut):-
    spec(signature(Sig, _)),
    
    % get the category for each constant in incompatibility substitutions.
    findall((C, CategoryC), 
                (member(C/vble(_), IncomSubs),
                 member((_,_,Arguments), Sig),
                 member(CategoryC, Arguments),
                 member(C, CategoryC)),
            Cat),
             
    upArgs(ArgDom, VbConsSC, ArgsAllF, IncomSubs, Cat, [], ArgsOut).
    /* TODO:    % Heuristic5: replace duplicate variables 
    findall((I,vble(X)), nth0(I,ArgsTem, vble(X)), VblePos),
    findall( (member((Num, Vble), VblePos)))*/
upArgs([], _, _, _, _, _, []):- !.
upArgs(ArgDom, _, _, _,_, Args, Args):-
    length(ArgDom, Arity),
    length(Args, Arity), !.

% when the rule is not involved in any proof of sufficiency.
upArgs(ArgDom, [], ArgsAllF, IncomSubs, Cat, ArgsIn, ArgsOut):- %pause,
    length(ArgsIn, I),        % have gotten Ith arguments, now to calculate the Ith
    nth0(I, ArgDom, AIDom), % get the domain of the Ith argument
    findall(vble(X),
            (member(C/vble(X), IncomSubs),
             member((C, CatC), Cat),
             intersection(AIDom, CatC, [_|_]),    % the constnat that the variable is bound is under the same category of the current argument
             notin(C, AIDom)),    % it should not occur in the domain, otherwise, the precondition is resolvable.
          VCand),
    (member(Arg, VCand);
     VCand = []-> member(Arg, AIDom)),
    append(ArgsIn, [Arg], ArgsNew), !,
    upArgs(ArgDom, [], ArgsAllF, IncomSubs, Cat, ArgsNew, ArgsOut).

% when the rule is involved in a proof of sufficiency.
upArgs(ArgDom, VbConsSC, ArgsAllF, IncomSubs, Cat, ArgsIn, ArgsOut):-
    length(ArgsIn, I),        % have gotten Ith arguments, now to calculate the Ith
    nth0(I, ArgDom, AIDom), % get the domain of the Ith argument
    findall(vble(X),
            (member((vble(X),ConsList), VbConsSC),
            forall(member(C, ConsList), member(C, AIDom))),
          VCand),
    % find all constants in the domain and the instantiated rule.
    findall(C,
            (member(C, AIDom),
             member(C, ArgsAllF)),
          CCand),

    (VCand = [_|_]-> member(Arg, VCand);            % Hueristic: the best choice is a variable
     VCand = [], CCand = [_|_]->member(Arg, CCand);    % the second is one constant which occurs in the instanti
     member(Arg, AIDom)),                            % the last is just one from its argument domain.
    append(ArgsIn, [Arg], ArgsNew),
    upArgs(ArgDom, VbConsSC, ArgsAllF, IncomSubs, Cat, ArgsNew, ArgsOut).
