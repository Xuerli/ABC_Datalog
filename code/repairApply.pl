:-[util].
:-import(lists).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%     APPLY   REPAIR   PLANS    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
/**********************************************************************************************************************
    appRepair(RsPlans, TheoryIn, RsBanIn, TheoryOut, RsBanOut): apply the repair plan to the theory.
    Input:     RsPlans: a list of repair plans to be applied.
            TheoryIn: the theory to which RsPlans will be applied.
            RsBanIn: the list of banned repair plans.
    Output: TheoryOut is the repaired theory. When the repair plan cannot be applied, TheoryOut = TheoryIn
            RsBanOut: updated the list of banned repair plans.
***********************************************************************************************************************/
appRepair(RepPlans, TheoryStateIn, TheoryStateOut):-
    writeLog([nl, write_term('-------- Start to apply repair plans:'), nl, write_termAll(RepPlans),nl,finishLog]),
    TheoryStateIn = [[RsIn, RsBanIn],EC, Eproof, TheoryIn, TrueSet, FalseSet],
    appRepair(RepPlans, TheoryIn, RsBanIn, TheoryOut, RsBanOut),
    append(RsIn, RepPlans, RsOut),
    TheoryStateOut = [[RsOut, RsBanOut],EC, Eproof, TheoryOut, TrueSet, FalseSet].
    
appRepair([], Theory, RsBan, Theory, RsBan):-!,
    writeLog([nl, write_term('-------- Finish applying repair plans.'), nl, finishLog]).
appRepair([Rs1|Rest], TheoryIn, RsBanIn, TheoryOut, RsBanOut):-
    appRepair(Rs1, TheoryIn, RsBanIn, TheoryTem, RsBanTem),
    verifyRep(TheoryIn, TheoryTem, Rs1, RsBanTem, RsBanTem2, TheoryTem2),
    appRepair(Rest, TheoryTem2, RsBanTem2, TheoryOut, RsBanOut).

%% Belief revision: delete unwanted clauses from the original Theory.
appRepair(delete(Clause), TheoryIn, RsBan, TheoryOut, RsBan):-
    delete(TheoryIn, Clause, TheoryOut), !.

appRepair(dele_pre(RulePairs), TheoryIn, RsBan, TheoryOut, RsBan):-
    replaceS(RulePairs, TheoryIn, TheoryOut),!.
    
%% add a new axiom
appRepair(expand(Clause), TheoryIn, RsBan, TheoryOut, RsBan):- !,
    sort([Clause| TheoryIn], TheoryOut).

appRepair(analogy(_, NewRule), TheoryIn, RsBan, TheoryOut, RsBan):- !,
    sort([NewRule| TheoryIn], TheoryOut).

%% turn an old assertion to a new rule
appRepair(ass2rule(Axiom, NewRule), TheoryIn, RsBan, TheoryOut, RsBan):-
    delete(TheoryIn, Axiom, TheoryTem),
    sort([NewRule|TheoryTem], TheoryOut), !.

%% add a new precondition to a rule
appRepair(add_pre(NewPrec, Rule), TheoryIn, RsBan, TheoryOut, RsBan):-
    sort([NewPrec| Rule], RuleNew),    % sort the clause where the head will be placed as the first literal.
    replaceS(Rule, RuleNew, TheoryIn, TheoryOut),!.
    

%% Apply weaken a variable to a constant.
appRepair(weaken(vble(X), TargCons, TargCl), TheoryIn, RsBan, TheoryOut, RsBan):-
    appEach(TargCl, [appLiteral, [replace, 2, vble(X), TargCons]], ClNew),
    replaceS(TargCl, ClNew, TheoryIn, TheoryOut), !.

appRepair(extC2V(X), TheoryIn, RsBanIn, TheoryOut, RsBanOut):-
    appRepair(rename(X), TheoryIn, RsBanIn, TheoryOut, RsBanOut).
%% Apply rename an item F which is either a predicate or a constant.
%% Rename includes blocks the unification of a proposition from PS and a input proposition.
%% Rename the Item in either side of the unification except the one from the preferred structure.
appRepair(rename(F, TargetL, TargetCl), TheoryIn, RsBanIn, TheoryOut, RsBanOut):-
    dummyTerm(F, TheoryIn, FNew),
    spec(protList(ProtectedList)),
    
    appLiteral(TargetL, [nth0, 1, Ith, F]),    % Get the position of the original argument vble(X).
    appLiteral(TargetL, [replacePos, 1, Ith, FNew], LitNew),
    replaceS(TargetL, LitNew, TargetCl, ClNew),
    orderAxiom(ClNew, ClNewSorted),
    replaceS(TargetCl, ClNewSorted, TheoryIn, TheoryOut),
    termOcc(F, TheoryOut, OccF),    % calculate the number occurances of F in the new theory.
    (OccF == 0, occur(F, ProtectedList)-> 
                writeLog([nl, write_term('******** Warning1: Cannot apply repair plan:'), 
                write_term(rename(F)),nl,
                write_term('--Otherwise the predicate is gone:'), nl, finishLog]),
                fail;    % F is gone, which is not allowed. Go to the last branch of appRepair
     OccF < 2, occur(F,ProtectedList)->
                 RsBanOut = [rename(F)| RsBanIn], writeLog([nl, write_term('******** Warning2 do not apply:'), 
                 write_term(rename(F)),nl, write_term(' more.'), nl, finishLog]),!;     % do not rename F further
     RsBanOut = RsBanIn, writeLog([nl, write_term('******** Finish renaming.'),nl, finishLog]),!).

appRepair(rename(_, _, InpClOld, ClNew), TheoryIn, RsBan, TheoryOut, RsBan):-
    replaceS(InpClOld, ClNew, TheoryIn, TheoryOut).
    
appRepair(rename(POld, PNew, Arity, LitOld, InpClOld, Opt), TheoryIn, RsBan, TheoryOut, RsBan):-
    appLiteral(LitOld, [mergeProp, 0, POld, PNew, Arity, Opt], LitNew),
    replaceS(LitOld, LitNew, InpClOld, InpClNew),
    replaceS(InpClOld, InpClNew, TheoryIn, TheoryOut).


% rename the constant Cold with CNew in clause ClOld.
appRepair(rename(RenameList), TheoryIn, RsBan, TheoryOut, RsBan):-
    appAll(appRename, RenameList, [TheoryIn], TheoryOut, 1).

% merge by make all F1's arity to be Arity, and then replacing all F1 with F2.
appRepair(merge(POld, PNew, ArgDiff, Op), TheoryIn, RsBan, TheoryOut, RsBan):-
    % replace all F1 with F2 at each proposition
    appEach(TheoryIn, [appEach, [appLiteral, [mergeProp, 0, POld, PNew, ArgDiff, Op]]], TheoryTem),
    appEach(TheoryTem, [sort], TheoryTem2),    % remove duplicate literals at each axiom.
    sort(TheoryTem2, TheoryOut).
    

appRepair(arityDec(PG, TargCls, PosMis), TheoryIn, RsBan, TheoryOut, RsBan):-
    writeLog([nl, write_term('-------- Start apply arityDec-------- '),nl, write_term(arityDec(PG, TargCls, PosMis)), finishLog]),
     % decrease the arity of PG by replacing the arguments which need to be deleted with [] and then delete [].
     findall((ClOld, ClNew),
                 (member(ClOld, TargCls),
                 findall((L, LNew), 
                             (member(L, ClOld),
                             (L = +[PG|Args],
                             replacePosList(PosMis, [PG|Args], [], PTem),
                             delete(PTem, [], PNew),
                             LNew = +PNew;
                             L = -[PG|Args],
                             replacePosList(PosMis, [PG|Args], [], PTem),
                             delete(PTem, [], PNew),
                             LNew = -PNew)), 
                         LitPairs),
                 replaceS(LitPairs, ClOld, ClNew)),
             ChangeClPairs),
     replaceS(ChangeClPairs, TheoryIn, TheoryOut).
     
%% Apply repair which increase the arity of P by 1, and give distinguished constants to propositions Pro1 and Pro2: arityInc([P|Args]).
%% The new arguments should BLOCK the targeted unwanted unification in Proof.
%% The input theory does not include propositions in preferred structure(PS).
%% Therefore, arityInc which blocks the unification of a proposition from PS and a input proposition will fail.
appRepair(arityInc(P, TargetL, TargetCl, _, PairCl), TheoryIn, RsBan, TheoryOut, RsBanNew):-
    writeLog([nl, write_term('-------- Start apply arityInc-------- '),nl,
        write_term(arityInc(P, TargetL, TargetCl)), finishLog]),
      
    % collect the existing dummy terms in the input theory.
    findall(Num, (member(Clause, TheoryIn),
                (member(+[P| Args], Clause);member(-[P| Args], Clause)),
                member([C], Args),
                string_concat('dummy_Normal', Num, C)),
            OldSer),
       sort(OldSer,  Sorted),
       
    % get dummy terms
    dummyTermArityInc(Sorted, DefCons, UniqCons),
    
    % Add unique constant/default constant to the targeted propositions and update them in the theory.
    % Heuristic6: When there are multiple occurrences of predicate, allocate them with same new argument while applying arity increment.
    findall((TLit, TLNew),
                (member(TLit, TargetCl), 
                (TLit = +[P|_]; TLit = -[P|_]),
                appLiteral(TLit, [append, 0, [[UniqCons]]], TLNew)), 
            TPairLis),
  
    replaceS(TPairLis, TargetCl, ClNew),
    % Get the desired arity of P, to avoid repeated arity increment in the following process.
    appLiteral(TargetL, [length, 0, PosNewArg]),     
    RsBan2 = [delete(ClNew), deleArg(P, PosNewArg)], 
    append(RsBan2, RsBan, RsBanNew),            % Heuristic: do not delete the unique instantce      
    
    findall((Lit, LNew),
                (member(Lit, PairCl), 
                (Lit = +[P|_]; Lit = -[P|_]),
                appLiteral(Lit, [append, 0, [[DefCons]]], LNew)), 
            PairLis),
    replaceS(PairLis, PairCl, PairClNew),
    
    replaceS([(TargetCl, ClNew), (PairCl, PairClNew)], TheoryIn, TheoryTem), 
    
    % Add the default constant/independent variables to all occurrences of P,
    % and get the list of targeting propagated predicates, which occur in a rule together with P.
    propArityInc([(P,1,PosNewArg)], TheoryTem, TheoryOut, [[DefCons]]).

appRename((COld, CNew, ClOld), TheoryIn, TheoryOut):-
    appEach(ClOld, [appLiteral, [replace, 2, COld, CNew]], ClNew),
    replaceS(ClOld, ClNew, TheoryIn, TheoryOut).

% construct dummy terms for appRepair(arityInc(P, TargetL, TargetCl)
dummyTermArityInc([], DefCons, UniqCons):-
    DefCons = dummy_Normal1, 
       UniqCons = dummy_Abnormal1, !.
       
dummyTermArityInc(Sorted, DefCons, UniqCons):-
    last(Sorted, Largest),
    NewSer is Largest +1,
    atom_string(NewSer, NewSerStr),
    appEach(['dummy_Normal_', 'dummy_Abnormal_'], 
           [string_concat, NewSerStr], [DefConsStr,UniqConsStr]),
    appEach([DefCons, UniqCons], [term_string], [DefConsStr, UniqConsStr]).

/**********************************************************************************************************************
    verifyRep(TheoryOld, TheoryNew, RepPlan, RsBanIn, RsBanOut): 
            verify whether the repair plan fails constraints. If yes, add RepPlan to RsBanIn.
    Input:     TheoryOld: the input theory before applying the repair plan.
            TheoryNew: the resulting theory after applying the repair plan.
            RepPlan: the applied repair plan.
            RsBanIn: the banned list of repair plans.
    Output: RsBanOut: the revised banned list of repair plans.
***********************************************************************************************************************/
verifyRep(Theory, Theory, RepPlan, RsBanIn, [RepPlan|RsBanIn], Theory):- !.    % the repair plan makes no difference
% no orphan variable allowed
verifyRep(TheoryOld, TheoryNew, RepPlan, RsBanIn, [RepPlan|RsBanIn], TheoryOld):-
    %  orphan Vb
    appEach(TheoryNew, [orphanVb], Ophans),  % X = [[],[],(AxiomOphan, Ophans),[]...]
    sort(Ophans, OpOrdered), % remove duplicates.
    % check that there should not be any axiom with orphan variable.
    flatten(OpOrdered, [_|_]), !,
    writeLog([nl, write_term('******** Warning: verifyRep found orphans:'), write_term(RepPlan),nl,
            nl, write_termAll(TheoryNew),nl, finishLog]).
    
% no protected axioms should gone.
verifyRep(TheoryOld, TheoryNew, RepPlan, RsBanIn, [RepPlan|RsBanIn], TheoryOld):-
    spec(protList(ProtectedList)),
    deleteAll(TheoryOld, TheoryNew, AxiomsGone),
    spec(protList(ProtectedList)),
    % deletion X is not allowed.
    (intersection(AxiomsGone, ProtectedList, [_|_]);
    member(X, AxiomsGone), 
    occur(delte(X), RsBanIn)), !,        
     % at least one protected axiom is gone due to the merge, which is not allowed. Go to the last branch of appRepair
    writeLog([nl, write_term('******** Warning: verifyRep:'), write_term(RepPlan),nl,
                write_term(' failed.'),nl, write_termAll(TheoryNew),nl, finishLog]).

% Heuristic4: no mirror rule is allowed
verifyRep(TheoryOld, TheoryNew, RepPlan, RsBanIn, [RepPlan|RsBanIn], TheoryOld):-
    setof([+Y,-X], (member([+X,-Y], TheoryNew), member([+Y,-X], TheoryNew)), LoopRule),    
    % at least one mirror rule is found.
    writeLog([nl, write_term('******** Warning: verifyRep found a loop rule:'), write_term(LoopRule), nl, finishLog]).
% Finish the verification.    
verifyRep(_, TheoryNew, _, RsBan, RsBan, TheoryNew). 

/*********************************************************************************************************************
    propArityInc(PropListIn, TheoryIn, TheoryOut, DefaultConstants): Get TheoryOut by propagation all arity increments on TheoryIn.
    Input:  PropListIn is the list of predicates, to which the arity increment needs to propagate.
            PredListIn: [(P1,N1,L1), (P2,N2,L2)...]: add Ni new arguments to the predicate Pi to get Li.
            TheoryIn is the input theory which has only the original clauses.
            DefCons is the default constants of these propagations.
    Output: TheoryOut is the repaired theory.
    Note:   Orphan variables: the variables only in the head of a rule, not in the body of that rule.
*********************************************************************************************************************/
% No predicate to propagate.
propArityInc([], Theory, Theory, _):- !.

propArityInc([(P, N, L)| PropList1], TheoryIn, TheoryOut, DefCons):-
    propArityIncTheo([add_n(P,N,L)], TheoryIn, TheoryTem, DefCons, [], PropList2),  % Increase the airty of P from N to L.
    append(PropList1, PropList2, PropList),
    propArityInc(PropList, TheoryTem, TheoryOut, DefCons).




%% ArgLast is the argument list which should be added as the new arguments to all the instances of predicate P.
%% PropList is the list of predicates to propgate the arity increment, because these predicates occur in the rules having P.
propArityIncTheo(_, [], [],_, PredList, PredList):- !.

propArityIncTheo([add_n(P,N,L)], [ClauseH| Rest], [ClauseR| RestNew], ArgLast, PredListIn, PredListOut):-
    propArityIncCl([add_n(P,N,L)], ClauseH, ClauseR, ArgLast, PredListIn, PredListTem),
    propArityIncTheo([add_n(P,N,L)],  Rest, RestNew, ArgLast, PredListTem, PredListOut).


mergeProp([POld| Args], POld, PNew, ArgDiff, inc, [PNew| ArgsNew]):-
    append(Args, ArgDiff, ArgsNew), !.
mergeProp([POld| Args], POld, PNew, ArgsG, dec, [PNew| ArgsNew]):-
    length(ArgsG, Arity),
    split_at(Arity, Args, ArgsNew,_), !.
mergeProp([POld| Args], POld, PNew, _, equ, [PNew| Args]):- !.
mergeProp(Prop, _, _, _, _, Prop).


/*********************************************************************************************************************************
    propArityIncCl(PredListIn, ClauseIn, ClauseOut, DefaultArgs, IndepVbles, PredListOut):
        increase the arity of predicate P by adding DefaultArgs to the original literals of predicate P.
    Input:  PredListIn is the list of predicates, to which the arity increment needs to propagate.
            PredListIn: [(P1,N1,L1), (P2,N2,L2)...]: add Ni new arguments to the predicate Pi to get Li.
            DefaultArgs: the list of N default constants for the new arguments.
            ClauseIn: an input clause.
    Output: ClauseOut: the repaired clause.
            IndepVbles: the list of independent variables for propagation.
            PredList [(Pred, AOrig, ATarg)]: the list of predicates from the body of a repaired rule.
            PredList is recorded for propagation to avoid orphan variable.
            AOrig is the original arity of the predicate Pred;
            ATarg is the targeted arity of the airty increment of predicate Pred.
    The format of a clause: [+[persecutes,[saul],[christians]]].
    TODO: consider whether  we should add independent variables to the literals in a rule?
**********************************************************************************************************************************/
% Nothing to repair.
propArityIncCl(_, [], [], _, _, PredList, PredList):- !.

% Add default constants as the new arguments to an assertion of P.
propArityIncCl([add_n(P, N, L)], [+[P | Args]], [+[P | ArgsOut]], DefArgs, PredList, PredList):-
    length(Args, M), L is M + N, append(Args, DefArgs, ArgsOut), !,
    spec(protList(ProtectedOld)),
    (member([+[P | Args]], ProtectedOld)->
        sort([[+[P | ArgsOut]]| ProtectedOld], ProtNew),
        retractall(spec(protList(_))),
        assert(spec(protList(ProtNew))),!; true).

% If the head of a rule contains P, then add new variables to it and one of the literals in its body.
propArityIncCl([add_n(P, N, L)], [+[P| Arg]| Body], [+[P| ArgNew]| BodyNew], _, PropListIn, PropListOut):-
    % The predicate of this rule's head is P, and its arity is not the desired L.
    length(Arg, M), 
    % To update the arity to L, N new independent variables need to be added to the head.
    L is M + N,
    gensymVble(N, IndepVbles),
    append(Arg, [IndepVbles], ArgNew), !,
    spec(protList(ProtectedList)),
    
    (    % if the target predicate also occurs in the body
        setof((-[P| ArgB], -[P| ArgNewB]),         % get a pair of old literal and its new literal by adding the new arguments.
                (member(-[P| ArgB], Body),
                 length(ArgB, M),
                  L is M + N, 
                 append(ArgB, [IndepVbles], ArgNewB)),
            BodyPairs)->        
        appAll(replaceS, BodyPairs, [Body], BodyNew, 1),    % replace the old ones with new ones. 
        PropListOut = PropListIn;
        
        % if the target predicate does not occur in the body
        notin(-[P| _], Body)->            % Otherwise, get the rest predicates in the body, the arity of one or them needs to increase by N for propagation. 
        setof((PredC, ArgsC, N, LTarg),                % If there is no such a predicate, fail. Because if IndepVbles occur only in the head of this repaired rule, they are orphan variables, not allowed in Datalog.
                  (member(-[PredC| ArgsC], Body),
                   PredC \= P,
                   notin(arity(PredC), ProtectedList),          % The predicate's arity is not protected from being changed.
                   length(ArgsC, LOrig),
                   LTarg is LOrig + N),                          % The targeted arity of the arity increment of the predicate.
          PropListNew),                                      % Get a list of predicates to propagate the arity increment with no redundancy.
        member((PT, ArgTarg, N, L1), PropListNew),                    % Get one predicate from the body of this rule, to which the airty increment needs to propagate.
        PropListOut = [(PT, N, L1)| PropListIn],
        append(ArgTarg, [IndepVbles], ArgNew1),
        % Get the propagated body of this rule.
        replaceS(-[PT| ArgTarg], -[PT| ArgNew1], Body, BodyNew)),

    % update the protected list.
    spec(protList(ProtectedOld)),
    (member([+[P| Arg]| Body], ProtectedOld)->
        sort([[+[P| ArgNew]| BodyNew]| ProtectedOld], ProtNew),
        retractall(spec(protList(_))),
        assert(spec(protList(ProtNew))), !; true).


% If the body of a rule contains P, then add new arguments(independent variables) to the literals of P.
% No further propagation needed.
propArityIncCl([add_n(P, N, L)], RuleIn, RuleOut, _, PropList, PropList):-
    (RuleIn = [+H| Body]; notin(+_, RuleIn), Body = RuleIn, H = []),
    % if the target predicate also occurs in the body
    setof((-[P| ArgB], -[P| ArgNewB]),         % get a pair of old literal and its new literal by adding the new arguments.
            (member(-[P| ArgB], Body),
             length(ArgB, M),
             L is M + N, 
             gensymVble(N, IndepVbles),     % Generate N independent variables.
             append(ArgB, [IndepVbles], ArgNewB)),
        BodyPairs),        
    appAll(replaceS, BodyPairs, [Body], BodyNew, 1),!,
    (H \= []-> RuleOut = [+H| BodyNew];
    H = []-> RuleOut = BodyNew),
    % update the protected list.
    spec(protList(ProtectedOld)),
    (member(RuleIn, ProtectedOld)->
        sort([RuleOut| ProtectedOld],ProtNew),
        retractall(spec(protList(_))),
        assert(spec(protList(ProtNew))),!; true).

% Nothing to change when predicate P does not occur in the Clause
propArityIncCl([add_n(_,_,_)], Clause, Clause, _, PredList, PredList).


/**********************************************************************************************************************
    repCombine(RepPlans, Theory, RepSolsOut):-
            update Group by revising Rep.
    Input:  RepPlans: the list of the collection of repair plans for each fault.
            Theory: the theory.
    Output: RepSolsOut: a list of solutions of repair plans. Each solution is the maximum group of independent repair plans.
************************************************************************************************************************/    
repCombine([], _, []):- !.
repCombine(RepPlans, Theory, RepSolsOut):-
    
    findall(RepS,    
                    (repCombine(RepPlans, Theory, [[]], RawSols), % RawSols is a collection of groups:[[[Rep1,Rep2...]]]
                     member(RawSol, RawSols),
                     findall(Rep, 
                                 (member([_,(RepS,_),_],RawSol),
                                  member(Rep, RepS)), 
                             RepS)),
            RepSolsTem),
    % get the group which is not contained by others. TODO: revise updGroup
    findall(Group,    
                    (member(Group, RepSolsTem),
                     Group = [_|_],
                     forall((member(r, RepSolsTem), Group2 \= Group),
                              deleteAll(Group, Group2, [_|_]))),
            RepSols),
    sort(RepSols, RepSolsOut),
    writeLog([nl, write_term('All collections of repair plans are: '), nl, write_termAll(RepSolsOut),nl, finishLog]).

    
repCombine([], _, Solutions, Solutions).
repCombine([Reps1| Rest], Theory, Groups, Solutions):- 
    % Reps1 is a list of repair plans for one fault.
    member(Rep1, Reps1),
    appEach(Groups, [updGroup, Rep1, Theory], GroupsTem),
    appAll(append, GroupsTem, [[]], GroupsNew, 1),
    repCombine(Rest, Theory, GroupsNew, Solutions).

/**********************************************************************************************************************
    updGroup(Group, Rep, Theory, GroupsOut):-
            update Group by revising Rep.
    Input:  Group: a group of repair plans, among which all members are independent from each other.
            Rep: the repair plans for fixing one fault, together with its information.
            Theory: the theory.
    Output: GroupsPair: a pair of groups.
************************************************************************************************************************/                 
updGroup([], Rep, _, [[Rep]]):- !.
updGroup(Group, Rep,Theory, GroupsOut):-
    Rep = [FType1, (_, TargCls1), Cl1],
    findall(RepS,         
                    (member(RepS, Group),
                    RepS = [FTypeS, (_, TargClsS), ClS],
                    repConflict(FType1, FTypeS, Theory, TargCls1, TargClsS, Cl1, ClS)),
                    %writeLog([nl,write_term('--Conflicts of repairs:'),nl, write_term(FType1),write_term(' vs '), write_term(FTypeS),nl, write_term(Rep),nl,write_term(RepS),nl, finishLog])),
            Confs),
    (Confs = [_|_]-> 
        deleteAll(Group, Confs, Fusion), !,
        Group2= [Rep| Fusion],
        sort([Group, Group2], GroupsOut);
    Confs = []->
        GroupsOut= [[Rep| Group]]).
    

/**********************************************************************************************************************
    repConflict(FType1, FType2, Theory, TargetCls1, TargetCls2, ClP1/ClE1, ClP2/ClE2):-
            check if repair plan 1 and 2 conflict with each other.
    Input:  RepPlans: the list of the collection of repair plans for each fault.
            Theory: the theory.
            TargetCls1: the targeted clauses which will be changed by applying repair plan 1
            TargetCls2:    the targeted clauses which will be changed by applying repair plan 2
            ClP1/ClE1:    the clauses of an incompatibility's proof/ the unprovable sub-goals of an insufficiency, which will be repaired by repair plan 1
            ClP2/ClE2:    the clauses of an incompatibility's proof/ the unprovable sub-goals of an insufficiency, which will be repaired by repair plan 2
    Output: None. terminate with success if repair plan 1 conflicts with repair plan 2.
***********************************************************************************************************************/

repConflict(incomp, incomp, _, TargetCls1, TargetCls2, ClP1, ClP2):- !,
    intersection(TargetCls1, ClP2, [_|_]), !; intersection(TargetCls2, ClP1, [_|_]).

% insuff vs insuff
repConflict(insuff, insuff, Theory, TargetCls1, TargetCls2, ClE1, ClE2):- 
    findall(P1, (member(Cl1, ClE1),
                 (member(+[P1|_], Cl1); member(-[P1|_], Cl1))),
            PCl1),
    findall(P2, (member(Cl2, ClE2),
                 (member(+[P2|_], Cl2); member(-[P2|_], Cl2))),
            PCl2),
                 
    (setof(Int,    
            ((member([+[P|_]|_], TargetCls1), !; [+[P|_]|_] = TargetCls1),
            extBranch([TargetCls1| Theory], [P], PBranch),    % get all predicates which is after P on their branches.
            intersection(PBranch, PCl2, Int),
            Int = [_|_]),
        Conflicts), !;    
    setof(Int,    
            ((member([+[P|_]|_], TargetCls2), !; [+[P|_]|_] = TargetCls2), 
            extBranch([TargetCls2| Theory], [P], PBranch),
            intersection(PBranch, PCl1, Int),
            Int = [_|_]),
        Conflicts)),
    writeLog([nl,write_term('--Conflicts of insuff vs insuff:'),write_term(Conflicts),nl, finishLog]).
    
repConflict(insuff, incomp, Theory, TargetCls1, TargetCls2, ClP1, ClP2):-
    repConflict(incomp, insuff, Theory, TargetCls2, TargetCls1, ClP2, ClP1).

% incomp vs insuff
repConflict(incomp, insuff, Theory, TargetCls1, TargetCls2, ClP1, ClP2):-
    intersection(TargetCls2, ClP1, [_|_]), !;
    intersection(TargetCls1, ClP2, [_|_]), !;
    findall(P2, (member(Cl2, ClP2),
                 (member(+[P2|_], Cl2); member(-[P2|_], Cl2))),
            PCl2),
    setof(Int,    
            (member([+[P|_]|_], TargetCls1), 
            extBranch(Theory, [P], PBranch),
            intersection(PBranch, PCl2, Int),
            Int = [_|_]),    % there is an axiom which constitutes the proof of repairing the insufficiency whose predicate is under the scope of P's influence
        Conflicts), 
    writeLog([nl,write_term('--Conflicts of incomp vs insuff:'),write_term(Conflicts),nl, finishLog]).    
