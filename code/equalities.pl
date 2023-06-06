:- [proof].


/**********************************************************************************************************************
    unaeMain(TheoryIn, OptStateRep): calculate equivalence classes and repair unae faults of the theory.
    Input:  TheoryIn: the input theory.
    Output: OptStateRep = [(TheoryState, InsufIncomp),....]
            TheoryState = [Repairs, EC, EProof, TheoryRep, TrueSetE, FalseSetE],
                Repairs: the applied repairs to fix unae faults.
                EC: the equivalence class.
                EProof: the proofs of all equ
                TheoryRep: the repaired theory where all constants are reps.
                TrueSetE/FalseE: the true/false set of the preferred structure where all constants have been replaced by their representatives.
            InsufIncomp = (Suffs, InSuffs, InComps), where
                        Suffs: the provable goals from pf(T).
                        InSuffs: the unprovable goals from pf(T).
                        InComps: the provable goals from pf(F).
************************************************************************************************************************/
% if there is no '=' or '\=' in the signature. Do not comput equivalence class.
unaeMain(TheoryIn, OptStateRep):-
    spec(signature(Predicates, Constants)),
    notin((=,_), Predicates), !,    % = is not in the signature
    findall([C], member(C,Constants), EC),    % initialise the equivalence classes
    minimal(TheoryIn, EC, [], MinimalT, []),
    spec(pft(TrueSet)),
    spec(pff(FalseSet)),
    TheoryState = [[[],[]], EC, [], MinimalT, TrueSet, FalseSet],
    % detect the faults of incompatibilities and insufficiencies.
    detInsInc(TheoryState, InsufIncomp),
    OptStateRep = [(TheoryState, InsufIncomp)].


unaeMain(TheoryIn, OptStateRep):- % This one is not run
    % replace equal variable in each axiom.
    appEach(TheoryIn, [repEquVab], Theory1),
    % replace constants in the theory and the preferred structure with their equality class representatives respectively.
    equClass(Theory1, ECState),
    writeLog([nl, write_term_c('---------The ECState are------'),
            write_term_All(ECState), finishLog]),

    TheoryState = ([]| ECState),    % initialise the repair as [].
    % calculate equivalence classes, and then detect the faults based on the preferred structure and UNAE.
    unaeFaultDet(TheoryState, TheoryFault),
    TheoryFault = [_, _, _, _, UnaeFaults, _],

    (UnaeFaults = [[],[],[]]->     % if the theory is fault free.
            OptStateRep = TheoryFault;
    % Otherwise, repair all the faults and terminate with a fault-free theory or failure due to out of the costlimit.
    UnaeFaults \= [[],[],[]]->
            findall(OptOut,
                    unaeTheoryRep(TheoryFault, OptOut),
                    OptStateRep)).

/**********************************************************************************************************************
    equClass(TheoryIn, TheoryStateOut): calculate equivalence classes and their proofs.
    Input:  TheoryIn: the input theory.
            *TrueSet: get the global variable of the intern record of the true set of the preferred structure.
            *FalseSet: get the global variable of the intern record of the false set of the preferred structure
    Output: EStateOut= [EqClasses, EAll, EProofs, TheoryNew, TrueSetNew, FalseSetNew]
                EqClasses: [[a],[b],...] -- defualt value a list of lists where each sublist contains one constant.
                           example: [[a,b,c], [e,h,r]], a=b=c, where a is the representative; e=h=r, where e is the representative.
                EProofs: the equalities and their proofs respectively, e.g., [([+[=, [c1], [c2]]], [Proof1, Proof2...]), ...]
                TheoryNew: the rewritten theory where all constants are reps.

************************************************************************************************************************/
equClass(TheoryIn, EStateOut):-
    spec(signature(_, Constants)),    % get the set of all constants in the signature of the input theory.
        findall([C], member(C,Constants), ECIni),    % initialise the equivalence classes
    updateEC((ECIni, []), TheoryIn, (EqClasses, EAll, EProofs), TheoryNew), % TheoryNew's constants are reps.
    % update the preferred structure and the theory by replacing constants wither their representatives.
    spec(pft(TrueSet)),
    spec(pff(FalseSet)),
    appEach(TrueSet, [appLiteral, [rewConsRep, EqClasses]], TrueSetNew),
    appEach(FalseSet, [appLiteral, [rewConsRep, EqClasses]], FalseSetNew),
    EStateOut= [EqClasses, EAll, EProofs, TheoryNew, TrueSetNew, FalseSetNew],

    writeLog([write_term_c('Complete equlities computation.'),
            nl, write_term_c('--------The Equality Class is:--------'),
            nl,write_term_All(EqClasses), finishLog]).

/**********************************************************************************************************************
    unaeFaultDet(TheoryStateIn, Output): detect unae faults.
    Input:  TheoryStateIn = [Repairs, EC, EProofs, [], Theory2, TrueSetNew, FalseSetNew],
                Repairs: the applied repairs.
                EC: the equivalence class.
                EProofs: proofs of EC.
                TheoryIn: the current theory to which Repairs have been applied.
    Output = [TheoryStateIn, IneqProofs, ETAll, FaultState, UnaeFaults, NumAllFaults], where:
                IneqProofs: the proofs of the inequality theorems.
                ETAll: the equality theorems derived by the thoery without applying the transitivity rule.
                FaultState = (Suffs, InSuffs, InComps), where
                            Suffs: the provable goals from pf(T).
                            InSuffs: the unprovable goals from pf(T).
                            InComps: the provable goals from pf(F).
                UnaeFaults = [(1, UNAEinc1), (2, UNAEinc2), (3, UNAEinc3)] the list of all unae fautls.
                NumAllFaults: the total number of all unae faults and insufficiencies and incompatibilities.
************************************************************************************************************************/
unaeFaultDet(TheoryStateIn, Output):-
    TheoryStateIn= [_, EC, EProofs, TheoryIn, TrueSetNew, _],
    spec(pft(TrueSet)),
    allTheoremsP(TheoryIn, \=, EC, IneqProofs),
    findall([+[=, C1, C2]], member(([+[=, C1, C2]], _), EProofs), ETAll),

    % F1. get the faults of the unprovable rep1=rep2 in the true setc
    findall((Index, [+[=, Rep1, Rep2]]),
            nth0(Index, TrueSetNew, +[=, Rep1, Rep2]),
            UNAEinc1),

    % F2. get the faults of the unprovable c\=c in the true set
    findall((Index, Rep, C1, C2),
            (nth0(Index, TrueSetNew, +[\=, Rep, Rep]),
             nth0(Index, TrueSet, +[\=, C1, C2])),
            UNAEinc2),

    % F3. get the faults of c1=c2 ^ c1\=c2
    findall((C1, C2, Eq),
            (member(([+[\=, C1, C2]], _), IneqProofs),
             member(Eq, EC),    % get one equivalenc class
             member(C1, Eq),    % C1  is in that equivalence class
             member(C2, Eq)),    % so is C2, then C1= C2
            UNAEinc3),

    % Get the proofs of sufficiencies of rep=rep in the true setc
    findall((E, Proofs),
            (nth0(Index, TrueSetNew, +[=, Rep, Rep]),
             nth0(Index, TrueSet, +[=, C1, C2]),
             equLinkPath(ETAll, C1, C2, [], Path),
             % the proof of E is a a part of the proof of C1=C2
             member(E, Path),
             member((E, Proofs), EProofs)),
            UnaeSuff),

    % get other incompatibilities and insufficiencies.
    detInsInc(TheoryStateIn, (Suffs, InSuffs, InComps)),
    appemd(UnaeSuff, Suffs, SuffAll),
    FaultState = (SuffAll, InSuffs, InComps),
    % calculate the total number of fautls
    flatten([UNAEinc1, UNAEinc2, UNAEinc3, InSuffs, InComps], AllFaults),
    appEach(AllFaults, [length],  NumAllFaults),
    % collect all UNAE faults.
    UnaeFaults = [(1, UNAEinc1), (2, UNAEinc2), (3, UNAEinc3)],
    Output = [TheoryStateIn, IneqProofs, ETAll, FaultState, UnaeFaults, NumAllFaults].

/**********************************************************************************************************************
    unaeRepair(FaultType, Fault, TheoryFaultsIn, RsNew, TheoryNew): generate repairs to fix FaultT whose type is Type.
    Input:  FaultType: a number among 1-3.
            Fault: the information of the fault to repair
            TheoryFaultsIn = (TheoryState, IneqProofs, InsufIncomp, UnaeFaults, _),
                TheoryState =  [Repairs, EqClasses, EProofs, Theory, TrueSet, FalseSet].
                InsufIncomp = (SuffAll, InSuffs, InComps),
   Output:     RsNew: the set of repairs includes the existed repairs and the new one.
               TheoryNew: the repaired theory which can prove the Assertion from the goal.
************************************************************************************************************************/
% F1. repair the faults of unprovable rep1=rep2 in the true set
unaeRepair(1, Fault, TheoryFaultsIn, RsNew, TheoryNew):-
     Fault = (_, [+[=, Rep1, Rep2]]),
     TheoryFaultsIn = [TheoryState, _, _, (Suffs,_,_), _, _],
     TheoryState = [_, _, _, TheoryIn, _, _],
     member([Rep1| CS1], EC),    % get the equivalenc classes of C1
     member([Rep2| CS2], EC),    % get the equivalenc classes of C2
     EC1 = [Rep1| CS1],
     EC2 = [Rep2| CS2],

     % the proof of any equality of a pair of members in EC1 and EC2 will make Rep1 = Rep2
     findall(([-[=, C1G, C2G]], Evis),
            (    member(C1G, EC1),
                member(C2G, EC2),
                 NegProp = [-[=, C1G, C2G]],
                % Get all proofs and failed proofs of the goal.
                findall(Evidence,
                        (slRL(NegProp, TheoryIn, EC, _, Evidence, [])),
                        Evis)),
            UnaeInsuff),
    % unblock any will solve the problem.
    member(EvUnaeIns, UnaeInsuff),
    buildProof(EvUnaeIns, TheoryState, Suffs, TheoryStateNew),
    TheoryStateNew = [RsNew, _, _, TheoryNew, _, _].

% F2. repair the faults of the unprovable rep \= rep in the true set
% TODO: or to build a proof of C1 \= C2.
unaeRepair(2, Fault, TheoryFaultsIn, RsNew, TheoryNew):-
    Fault = (_, Rep, C1, C2),
    TheoryFaultsIn = [TheoryState, _, ETAll, (Suffs,_,_), _, _],
    TheoryState = [_, _, EProofsIn, _, _, _],

    % target at one path to Rep.
    (    equLinkPath(ETAll, C1, Rep, [], PathT);
         equLinkPath(ETAll, C2, Rep, [], PathT)),
    % target equlity to break is one in the target path.
    member(E, PathT),
    member((E, UnwProofs), EProofsIn),
    member(UnwProof, UnwProofs),
    % generate a repair to block the unwanted proof UnwProof.
    blockProof(UnwProof, TheoryState, Suffs, TheoryStateNew),
    TheoryStateNew = [RsNew, _, _, TheoryNew, _, _].

% F3. repair the faults of c1=c2 ^ c1\=c2
unaeRepair(3, Fault, TheoryFaultsIn, RsNew, TheoryNew):-
    Fault = (C1, C2, [Rep|_]),
    TheoryFaultsIn = [TheoryState, IneqProofs, ETAll, (Suffs,_,_), _, _],
    TheoryState = [_, _, EProofsIn, _, _, _],

    % get a set of unwanted proofs, which are either for C1 = C2 or for C1 \= C2.
    (    % block the proof of C1 = C2
        (    equLinkPath(ETAll, C1, Rep, [], PathT);
            equLinkPath(ETAll, C2, Rep, [], PathT)),
        % target equlity to break is one in the target path.
        member(E, PathT),
        member((E, UnwProofs), EProofsIn);
        % or block the proof of C1 \= C2
        member(([+[\=, C1, C2]], UnwProofs), IneqProofs)),
    % target at one unwanted proof
    member(TProof, UnwProofs),
    % generate a repair to block the targeted unwanted proof: TProof.
    blockProof(TProof, TheoryState, Suffs, TheoryStateNew),
    TheoryStateNew = [RsNew, _, _, TheoryNew, _, _].

/**********************************************************************************************************************
    unaeTheoryRep(TheoryFaultsIn,  OptStateOut):
            repair the theory w.r.t. the unae faults and output the unae fault-free EC and theory
    Input:  TheoryFaultsIn = [TheoryState, IneqProofs, ETAll, InsufIncomp, UnaeFaults, NumAllFaults]
                TheoryState = [RepairsIn, ECIn, EProofsIn, TheoryIn, TrueSetIn, FalseSetIn],
                IneqProofs: the proofs of the inequality theorems.
                ETAll: the equality theorems derived by the theory without applying the transitivity rule.
                InsufIncomp = (Suffs, Insuffs, Incomps), where  Insuffs and Incomps are the information about the insufficiencies and incompatibilities respectively.
                UnaeFaults:  The unae faults in five types.
            IneqProofs: the proofs of inequality theorems.
    Output: OptOut = (TPState, InsufIncomp)
                TPState =  [RepairsNew, ECNew, EProofsNew, TheoryNew, TrueSetNew, FalseSetNew], the theory, preferred structure and equivalence classes after repairing all unae faults.
                TheoryNew: the repaied theory without unae faults.
            InsufIncomp = (Suffs, InSuffs, InComps), where
                        Suffs: the provable goals from pf(T).
                        InSuffs: the unprovable goals from pf(T).
                        InComps: the provable goals from pf(F).
************************************************************************************************************************/
unaeTheoryRep(State, _, (TPState, InsufIncomp)):-
    State = (TPState, _, _, InsufIncomp, UnaeFaults, _),
    UnaeFaults = [[],[],[]], !. % no unae faults left.

unaeTheoryRep(TheoryFaultsIn, OptOut):-
    TheoryFaultsIn = [_, _, _, _, UnaeFaults, _],
    % get all possible repairs of all detected unae faults.
    findall(TheoryFaultsNew,
            (member((Type, Faults), UnaeFaults),
             member(FaultT, Faults),    % target at one fault.
             unaeRepair(Type, FaultT, TheoryFaultsIn, TheoryNew, RsNew),
             equClass(TheoryNew, TheoryStateNew),
             unaeFaultDet([RsNew| TheoryStateNew], TheoryFaultsNew)),
            TheoryFaultsAll),

    % get the optimal
    unaeOptimal(TheoryFaultsAll, Optimals),
    % continue with one optimal repair.
    member(StateOptimal, Optimals),

    % calculate equivalence classes, and then detect the faults based on the preferred structure and UNAE.
    unaeTheoryRep(StateOptimal, OptOut).

/**********************************************************************************************************************
    unaeOptimal(TheoryFaultsAll,  Optimals): Return the optimal which are not dominated by others.
    Input:  TheoryFaultsAll = [[_, _, _, _, _, NumAllFaults],...]
                NumAllFaults=[N1, N2, N3,N4, N5]:  The numbers of unae faults in five types.
    Output: Optimals =[[_, _, _, _, _, NumAllFaults],...]
************************************************************************************************************************/
% if the sub-optimal pruning is not applied, return the input.
unaeOptimal(TheoryFaults, TheoryFaults):-
    spec(heuris(H)),
    member(noOpt, H), !.

% otherwise, pruning the sub-optimal and only return the optimal ones.
unaeOptimal(TheoryFaultsIn, TheoryFaultsOpt):-
    findall(TF,
            (member(TF, TheoryFaultsIn),
             TF = [_,_,_,_,_, NumFaults1],
             % The repaired theory is not strictly dominated by any others.
             forall(member([_,_,_,_,_,NumFaults2], TheoryFaultsIn),
                     \+strDominated(NumFaults2, NumFaults1))),
            TheoryFaultsOpt),
    writeLog([nl, write_term_c('---------The UNAE Optimals are------'),
            write_term_All(TheoryFaultsOpt), finishLog]).

/**********************************************************************************************************************
    updateEC((ECOld, EProofsOld), TheoryIn, (ECNew, EProofsNew)): update equivalence classes and their proofs.
    Input:  ECOld:  The old equivalence classes.
            EProofsOld: the proof of the old equivalence classes.
            TheoryIn: the current input theory.
    Output: ECNew: The new equivalence classes.
            EProofsNew: the proof of the new equivalence classes.
            TheoryOut: output theory where all constants are replaced by their reps.
************************************************************************************************************************/
updateEC((ECOld, EProofsOld), TheoryIn, (ECNew, EProofsNew), TheoryOut):-
    % get all of the equalities and their proofs based on the current equivalence classes.
    allTheoremsP(TheoryIn, =, ECOld, EProofsCur),

    (% no new equalities are found
     forall(member(([+[=, C1, C2]], _), EProofsCur),
            equalSub(C1, C2, ECOld, []))->     % C1 and C2 are equal according to the old equivalence classes.
            ECNew = ECOld, EProofsNew =  EProofsOld, !;
     % new equalities are found
     findall([[C1, C2], NewE],
                  (member(([+[=, C1, C2]], Proofs), EProofsCur),
                 \+equalSub(C1, C2, ECOld, []),    % new equality is found
                 NewE = ([+[=, C1, C2]], Proofs)),
             NewE),     % update equality classes.

    transposeF(NewE, [NewPairs, NewEProofs]),
    % update EC from ECOld to ECNew.
    appAll(makeEqual, NewPairs, ECOld, ECNew, 2),
    % update the theory by rewriting all constants with their reps based on ECNew.
    appEach(TheoryIn, [appEach, [appLiteral, [rewConsRep, ECNew]]], TheoryNew),

    append(EProofsOld, NewEProofs, EPNew),
    updateEC((ECNew, EPNew), TheoryNew, (ECNew, EProofsNew), TheoryOut)).    % keep updating EC until no new eqaulities are found.

/**********************************************************************************************************************
    * These predicates will be used for constants and variables respectively.
    checkEqual(C1, C2, EqClasses): true when C1==C2 based on the EqClasses.
    makeEqual([C1, C2], EqClasses): make C1 and C2 in one equal list in the EqClasses
************************************************************************************************************************/
% Combine the equality lists of C1 and C2.
makeEqual([C1, C2], EqClasses, ECNew):-
    % get the lists of constants that equal C1 OR C2.
    setof([EquConts, C],
          (member(EquConts, EqClasses),
           (member(C1, EquConts);member(C2,EquConts)),
           member(C, EquConts)),
        EquCAll), !,
    transposeF(EquCAll, [EquClOld, EquCons]),
    sort(EquCons, ECNew),    % sort and remove duplicates
    deleteAll(EqClasses, EquClOld, RestECs),    % get the other equality lists that do not contain c1 neither c2.
    ECNew =  [ECNew| RestECs].    % update equality classes.

% check whether C1 equal C2
checkEqual(C1, C2, EqClasses):-
    setof(EqClass,
        (member(EqClass, EqClasses),
         member(C1, EqClass),
         member(C2, EqClass)),
        _).

/**********************************************************************************************************************
rewConsRep(Proposition, EClasses, Output): in a proposition, replace each constant with its representative based on the equality classes EClasses.
Input:     Proposition is a list, e.g., [mum, [diana], [william]].
        EClasses is a list of equalities, e.g., [[di, diana],[c, c2, c3], [william]].
Output: Output = [mum, [di], [william]].
************************************************************************************************************************/
% Nothing to replace, return the output.
rewConsRep([], _, []):-!.
% If it is a constant, attach it to its representative.
rewConsRep([C| Rest], EClasses, [Rep|OutputRest]):-
    member(EClass, EClasses),
    member(C, EClass),
    EClass = [Rep| _], !,
    rewConsRep(Rest, EClasses, OutputRest).
% Otherwise, continue to the next term.
rewConsRep([Term| Rest], EClasses, [Term|OutputRest]):-
    rewConsRep(Rest, EClasses, OutputRest).


/**********************************************************************************************************************
    repEquVab(Input,Output): When precondition v=t or t=v is in a rule, it is removed
                           by replacing all of the occurrences of v by t in that rule (v↦t).
    Input: AxiomIn is a list of literals, e.g., [+[=, vble(x), vble(y)],-[mum, vble(x),vble(z)],-[mum, vble(y), vble(z)]].
    Output: AxiomOut
************************************************************************************************************************/
repEquVab([], []):- !.
repEquVab(Axiom, AxiomOut):-
    setof([vble(X), vble(Y)],            % make each variable in a list form.
          member(-[=, vble(X), vble(Y)], Axiom),
          EquPairLists), !,   % get all equalities of variables in the axiom.
    appAll(makeEqual, EquPairLists, EquPairLists, NewEqualVabLists, 2),    % update the variables' equality class.
    writeLog([nl,write_term_c('--------------------NewEqualVabLists ---------------------'),nl,
            write_term_c(NewEqualVabLists), finishLog]),
    appEach(Axiom, [appLiteral, [rewConsRep, NewEqualVabLists]], AxiomOut),
    writeLog([nl,write_term_c('--------------------AxiomNew ---------------------'),nl,
            write_term_c(AxiomOut), finishLog]).

repEquVab(Axiom, Axiom).


/**********************************************************************************************************************
    equalSub(Equalitiy/Inequality, EC, Subs): get the substitution Subs which makes the Equality/Inequality true based on EC.
    Input:     Equalitiy/Inequality: a proposition of an equalitiy/inequality.
            EC: equivalence class.
    Output: Subs: the substitution which makes the Equality/Inequality true based on EC.
************************************************************************************************************************/
% for equalities.
equalSub([=, [X], [X]], _, []):-!.
equalSub([=, [X], [Y]], EC, Subs):-
    X \= Y,
    findall( Eq, (member(Eq, EC),
                member([X], Eq),
                member([Y], Eq)),
            Es), !,    % get the equivalence class which contains both constants.
    (Es = [] -> fail; Es \= [] -> Subs= []).

equalSub([=, vble(X), [Y]], _, [[Y]/vble(X)]):-!.
equalSub([=, [X], vble(Y)], _, [[X]/vble(Y)]):-!.
equalSub([=, vble(X), vble(X)], _, []):- !.
equalSub([=, vble(X), vble(Y)], _, [vble(X)/vble(Y)]):-
    X \= Y, !.

% for inequalities
equalSub([\=, X, Y], _, Subs):-
    is_cons(X), is_cons(Y),
    (X \= Y -> Subs= []; X = Y -> fail), !.
equalSub([\=, vble(Y), [X]], EC, Subs):-
    equalSub([\=, [X], vble(Y)], EC, Subs), !.
equalSub([\=, [X], vble(Y)], EC, [Z/vble(Y)]):-
    atomic(X),
    member(Eq, EC), notin([X], Eq), % get an equivalence class which does not have constant [X].
    member(Z, Eq).
equalSub([\=, vble(X), vble(Y)], EC, [Z1/vble(X), Z2/vble(Y)]):-
    member(Eq1, EC),
    member(Eq2, EC),
    Eq1 \= Eq2,
    member(Z1, Eq1),
    member(Z2, Eq2).


/**********************************************************************************************************************
equLinkPath(EList, C1, C2, VList): Find the valid path for C1=C2 based on EList
Input:  EList is a list of equalities
        C1 and C2 are constants.
Output: VList is a path from C1 to C2, e.g., [[+[=, [c1], [c3]],[+[=, [c3], [c4]]],[+[=, [c2], [c4]]]]
************************************************************************************************************************/
equLinkPath(_, C2, C2, VOut, VOut).
equLinkPath(EList, C1, C2, VIn, VOut):-
    setof(([+[=|Arg]], C3),
            (member([+[=|Arg]], EList),
             notin([+[=|Arg]], VIn),
             member(C1, Arg),
             delete(Arg, C1, [C3])),
            NextNodes),
    member((Eq, CNext), NextNodes),
    equLinkPath(EList, CNext, C2, [Eq|VIn], VOut).
