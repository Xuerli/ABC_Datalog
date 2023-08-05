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
    writeLog([nl, write_term_c('-------- Start to apply repair plans:'), nl, write_term_All(RepPlans),nl,finishLog]),
    nl, write_term_c('-------- Start to apply repair plans:'), nl, write_term_All(RepPlans),nl,
    TheoryStateIn = [[RsIn, RsBanIn],EC, Eproof, TheoryIn, TrueSet, FalseSet],
    appRepair(RepPlans, [], TheoryIn, RsBanIn, TheoryOut, RsBanOut, RsApplied),
    append(RsIn, RsApplied, RsOut),
    TheoryStateOut = [[RsOut, RsBanOut],EC, Eproof, TheoryOut, TrueSet, FalseSet].

appRepair([], RsApplied, Theory, RsBan, Theory, RsBan, RsApplied):-!,
    writeLog([nl, write_term_c('-------- Finish applying repair plans.'), nl, finishLog]).

appRepair([Rs1|Rest], RsAppliedIn, TheoryIn, RsBanIn, TheoryOut, RsBanOut, RsApplied):-
    appRepair(Rs1, TheoryIn, RsBanIn, TheoryTem, RsBanTem),
    verifyRep(TheoryIn, RsAppliedIn, TheoryTem, Rs1, RsBanTem, RsBanTem2, TheoryTem2, RsAppliedInNew),  
    sort(TheoryTem2, TheoryTem3),
    appRepair(Rest, RsAppliedInNew, TheoryTem3, RsBanTem2, TheoryOut, RsBanOut, RsApplied).

%% Belief revision: delete unwanted clauses from the original Theory.
appRepair(delete(Clause), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified
    delete(TheoryIn, Clause, TheoryOut), !.

appRepair(dele_pre(RulePairs), TheoryIn, RsBan, TheoryOut, RsBan):-
    replaceS(RulePairs, TheoryIn, TheoryOut),!.

%% add a new axiom
appRepair(expand(Clause), TheoryIn, RsBan, TheoryOut, RsBan):- !,
    sort([Clause| TheoryIn], TheoryOut).

appRepair(analogy(_, NewRule), TheoryIn, RsBan, TheoryOut, RsBan):- !,
    sort([NewRule| TheoryIn], TheoryOut).

%% turn an old assertion to a new rule
appRepair(ass2rule(Axiom, NewRule), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified
    delete(TheoryIn, Axiom, TheoryTem),
    sort([NewRule|TheoryTem], TheoryOut), !.

appRepair(cons2rule(Axiom, NewRule), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified
    delete(TheoryIn, Axiom, TheoryTem),
    sort([NewRule|TheoryTem], TheoryOut), !.

%% add a new precondition to a rule
appRepair(add_pre(NewPrec, Rule), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified.
    sort([NewPrec| Rule], RuleNew),    % sort the clause where the head will be placed as the first literal.
    replaceS(Rule, RuleNew, TheoryIn, TheoryOut),!.

appRepair(add_preP(NewPrec, Rule), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified.
    appRepair(add_pre(NewPrec, Rule), TheoryIn, RsBan, TheoryOut, RsBan),!. %THey are the same


%% Apply weaken a variable to a constant, unless it results in a rule with no variables.
appRepair(weaken(vble(X), TargCons, TargCl), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified
    appEach(TargCl, [appLiteral, [replaceNested, 2, vble(X), TargCons]], ClNew),
    findall(vble(Y), 
        (
            (member(+Prop, ClNew); member(-Prop, ClNew)), 
            memberNested(vble(Y), Prop)
        ),
    RemainingVbles),
    (RemainingVbles = []-> TheoryOut = TheoryIn,
     writeLog([nl, write_term_c('********  Warning : a rule without variables is resulted, so refuse the repair: '), nl,write_term_c(weaken(vble(X), TargCons, TargCl)),nl,finishLog]);
    RemainingVbles \= [], replaceS(TargCl, ClNew, TheoryIn, TheoryOut), !).

% extend to variable
appRepair(extC2V(MisPairs), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified.
    substC2V(MisPairs,TheoryIn,TheoryOut).

appRepair(renamePred(P,NewP,TargP,TargCl),TheoryIn, RsBan,TheoryOut,RsBan):- %Verified.
    prop(TargP,[P|OrgArgs]),
    addSameSign(TargP,[NewP|OrgArgs],NewPred),
    replaceS(TargP,NewPred,TargCl,NewCl),
    replaceS(TargCl,NewCl,TheoryIn,TheoryOut),!.


%% Apply rename an item F which is either a predicate or a constant.
%% Rename includes blocks the unification of a proposition from PS and a input proposition.
%% Rename the Item in either side of the unification except the one from the preferred structure.

%Renaming constants to BREAK a proof
appRepair(rename(F, TargetL, TargetCl), TheoryIn, RsBanIn, TheoryOut, RsBanOut):- %Verified.
    dummyTerm(F, TheoryIn, FNew),
    spec(protList(ProtectedList)),

    appLiteral(TargetL, [nth0, 1, Ith, F]),    % Get the position of the original argument vble(X).
    appLiteral(TargetL, [replacePos, 1, Ith, FNew], LitNew),
    replaceS(TargetL, LitNew, TargetCl, ClNew),
    orderAxiom(ClNew, ClNewSorted),
    replaceS(TargetCl, ClNewSorted, TheoryIn, TheoryOut),
    termOcc(F, TheoryOut, OccF),    % calculate the number occurances of F in the new theory.
    (OccF == 0, occur(F, ProtectedList)->
                writeLog([nl, write_term_c('******** Warning1: Cannot apply repair plan:'),
                write_term_c(rename(F)),nl,
                write_term_c('--Otherwise the predicate is gone:'), nl, finishLog]),
                fail;    % F is gone, which is not allowed. Go to the last branch of appRepair
     OccF < 2, occur(F,ProtectedList)->
                 RsBanOut = [rename(F)| RsBanIn], writeLog([nl, write_term_c('******** Warning2 do not apply:'),
                 write_term_c(rename(F)),nl, write_term_c(' more.'), nl, finishLog]),!;     % do not rename F further
     RsBanOut = RsBanIn, writeLog([nl, write_term_c('******** Finish renaming.'),nl, finishLog]),!).

% Renaming a predicate to BUILD a proof.
appRepair(rename(_, _, InpClOld, ClNew), TheoryIn, RsBan, TheoryOut, RsBan):- %Verified
    replaceS(InpClOld, ClNew, TheoryIn, TheoryOut).

%Reform one to the other completely (to BUILD a proof)
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

%Fail the occurs check
appRepair(occurFailC(TargLit,NewLit,TargCl),TheoryIn,RsBan,TheoryOut,RsBan):- %Verified
    replaceS(TargLit,NewLit,TargCl,NewCl),
    replaceS(TargCl,NewCl,TheoryIn,TheoryOut).

appRepair(occurFailF(FuncN,TargLit,NewLit,TargCl),TheoryIn,RsBan,TheoryOut,RsBan):- 
    replaceS(TargLit,NewLit,TargCl,NewCl),
    replaceS(TargCl,NewCl,TheoryIn,TheoryTmp),
    newArity(NewLit,FuncN,N),
    addArityP(TheoryTmp,FuncN,N,TheoryOut).

%Repair Occurs check
appRepair(repairOccurs(TargProp,NewProp,FuncN,DelPos,TargCl),TheoryIn,RsBan,TheoryOut,RsBan):- %Verified
    member(X,TargCl),
    (X = +TargProp; X = -TargProp),
    addSameSign(X,NewProp,SNewProp),
    replaceS(X,SNewProp,TargCl,NewCl),
    replaceS(TargCl,NewCl,TheoryIn,TheoryTmp),
    newArity(SNewProp,FuncN,N),
    deleteArityP(TheoryTmp,FuncN,DelPos,N,TheoryOut).


appRepair(arityDec(PG, TargCls, PosMis), TheoryIn, RsBan, TheoryOut, RsBan):-
    writeLog([nl, write_term_c('-------- Start apply arityDec-------- '),nl, write_term_c(arityDec(PG, TargCls, PosMis)), finishLog]),
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
appRepair(arityInc(P, TargetL, TargetCl, _, PairCl), TheoryIn, RsBan, TheoryOut, RsBanNew):- %Verified.
    writeLog([nl, write_term_c('-------- Start apply arityInc-------- '),nl,
        write_term_c(arityInc(P, TargetL, TargetCl)), finishLog]),

    % collect the existing dummy terms in the input theory.
    findall(Num, (member(Clause, TheoryIn),
                (member(+[P| Args], Clause);member(-[P| Args], Clause)),
                memberNested([C], Args),
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


/**********************************************************************************************************************
    verifyRep(TheoryOld, TheoryNew, RepPlan, RsBanIn, RsBanOut):
            verify whether the repair plan fails constraints. If yes, add RepPlan to RsBanIn.
    Input:     TheoryOld: the input theory before applying the repair plan.
            TheoryNew: the resulting theory after applying the repair plan.
            RepPlan: the applied repair plan.
            RsBanIn: the banned list of repair plans.
    Output: RsBanOut: the revised banned list of repair plans.
***********************************************************************************************************************/
verifyRep(Theory, RsAppliedIn, Theory, RepPlan, RsBanIn, [RepPlan|RsBanIn], Theory, RsAppliedIn):- !.    % the repair plan makes no difference

% no orphan variable allowed
% verifyRep(TheoryOld, RsAppliedIn, TheoryNew, RepPlan, RsBanIn, [RepPlan|RsBanIn], TheoryOld, RsAppliedIn):-
%     %  orphan Vb
%     appEach(TheoryNew, [orphanVb], Ophans),  % X = [[],[],(AxiomOphan, Ophans),[]...]
%     sort(Ophans, OpOrdered), % remove duplicates.
%     % check that there should not be any axiom with orphan variable.
%     flatten(OpOrdered, [_|_]), !,
%     writeLog([nl, write_term_c('******** Warning: verifyRep found orphans:'), write_term_c(RepPlan),nl,
%             nl, write_term_All(TheoryNew),nl, finishLog]).

% no protected axioms should gone.
verifyRep(TheoryOld, RsAppliedIn, TheoryNew, RepPlan, RsBanIn, [RepPlan|RsBanIn], TheoryOld, RsAppliedIn):-
    writeLog([nl, write_term_c('******** RepPlan: '), write_term_c(RepPlan),nl]),
    RepPlan \= arityInc(_,_,_,_,_),
    spec(protList(ProtectedList)),
    deleteAll(TheoryOld, TheoryNew, AxiomsGone),
    spec(protList(ProtectedList)),
    % deletion X is not allowed.
    (intersection(AxiomsGone, ProtectedList, [_|_]);
    member(X, AxiomsGone),
    occur(delte(X), RsBanIn)), !,
     % at least one protected axiom is gone due to the merge, which is not allowed. Go to the last branch of appRepair
    writeLog([nl, write_term_c('******** Warning: verifyRep:'), write_term_c(RepPlan),nl,
                write_term_c(' failed.'),nl, write_term_All(TheoryNew),nl, finishLog]).

% Heuristic4: no mirror rule is allowed
verifyRep(TheoryOld, RsAppliedIn, TheoryNew, RepPlan, RsBanIn, [RepPlan|RsBanIn], TheoryOld, RsAppliedIn):-
    setof([+Y,-X], (member([+X,-Y], TheoryNew), member([+Y,-X], TheoryNew)), LoopRule),
    % at least one mirror rule is found.
    writeLog([nl, write_term_c('******** Warning: verifyRep found a loop rule:'), write_term_c(LoopRule), nl, finishLog]).

% Finish the verification.
verifyRep(_, RsAppliedIn, TheoryNew, RepPlan, RsBan, RsBan, TheoryNew, [RepPlan|RsAppliedIn]).

/**********************************************************************************************************************
    repCombine(RepPlans, Theory, RepSolsOut):-
            update Group by revising Rep.
    Input:  RepPlans: the list of the collection of repair plans for each fault.
            Theory: the theory.
    Output: RepSolsOut: a list of solutions of repair plans. Each solution is the maximum set of communative repair plans.
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
    writeLog([nl, write_term_c('All collections of repair plans are: '), nl, write_term_All(RepSolsOut),nl, finishLog]).


repCombine([], _, Solutions, Solutions).
repCombine([Reps1| Rest], Theory, Groups, Solutions):-
    % Reps1 is a list of repair plans for one fault.
    member(Rep1, Reps1), %Rep1 is one possible repair plan.
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
                    %writeLog([nl,write_term_c('--Conflicts of repairs:'),nl, write_term_c(FType1),write_term_c(' vs '), write_term_c(FTypeS),nl, write_term_c(Rep),nl,write_term_c(RepS),nl, finishLog])),
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
    writeLog([nl,write_term_c('--Conflicts of insuff vs insuff:'),write_term_c(Conflicts),nl, finishLog]).

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
    writeLog([nl,write_term_c('--Conflicts of incomp vs insuff:'),write_term_c(Conflicts),nl, finishLog]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
substC2V([],Theory,Theory):- !. %Nothing then no need change.
substC2V([(COrig,Var,OrgCl)|R],TheoryIn,TheoryOut):-
    replaceNested(COrig,Var,OrgCl,NewCl),
    replaceS(OrgCl,NewCl,TheoryIn,TheoryTmp),
    replaceCls(R,OrgCl,NewCl,R2),
    substC2V(R2,TheoryTmp,TheoryOut).

replaceCls([],_,_,[]).
replaceCls([(COrig,Var,OrgCl)|R],OrgCl,NewCl,[(COrig,Var,NewCl)|R2]):-
    replaceCls(R,OrgCl,NewCl,R2).