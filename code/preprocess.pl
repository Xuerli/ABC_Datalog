
/*
Date: 19.02.2020

*/


:-[util, repairApply].
:-     maplist(dynamic, [trueSet/1, falseSet/1, heuristics/1, protect/1,spec/1]).

/**********************************************************************************************************************
    initTheory(Theory): Read Theory from a collection of axiom assertions. (Expected format of the Theory.)
        Output:    Theory is all the sentences that in the input theory and the preferred structure.
                   EqClasses: equal classes. An equal class is a list of equal constants.
                   Inequality Set: a list of constants which are unequal to each other based on UNAE.
***********************************************************************************************************************/
initTheory(Theory):-
    specification,
    % Convert each clause to internal representation convention.
    % Notice that only the ones within [] is a clause, others could be heuristics, e.g., axiom(una).
    findall(ClOut,
                (axiom(Axiom),
                convertClause(Axiom, Cl),
                orderAxiom(Cl, ClOut)),
            TheoryRaw),
    sort(TheoryRaw, Theory), % do not change the literal order in an axiom.
    % get the theory graph based on rules.
    theoryGraph(Theory, Graph),
    findall(ConvPClause,
            ( (    trueSet(Trues), member(Cl,Trues), Cl\=[];
                % convert the equalities and inequalities in False set to True set.
                falseSet(Falses), (    member((C1=C2),Falses), Cl=(C1\=C2);
                                    member((C1\=C2),Falses), Cl=(C1=C2))),
            convertClause([+Cl], ConvPClause)),
            TrueSet),
    findall(ConvVClause,
            (    falseSet(Falses), member(Cl,Falses),
                Cl\=[], Cl\= (C1=C2), Cl\= (C1\=C2),    % skip the equalities and inequalities.
                convertClause([+Cl], ConvVClause)),
            FalseSet),   % convert each axiom to internal representation
    appEach(Theory, [orphanVb], Ophans),  % X = [[],[],(AxiomOphan, Ophans),[]...]
    sort(Ophans, OpOrdered), % remove duplicates.
    % check that there should not be any axiom with orphan variable.
    flatten(OpOrdered, []),
    maplist(assert, [spec(tgraph(Graph)), spec(pft(TrueSet)), spec(pff(FalseSet))]),
    recSignature(Theory),
    % Initialise the protected list and heuristics.
    initProtList,
    heuristics(HeursOld),
    (member(noRuleChange, HeursOld)->
        append([noPrecAdd, noPrecDele, noAss2Rule, noAnalogy], HeursOld, HeursNew),
        assert(spec(heuris(HeursNew))),!;
        assert(spec(heuris(HeursOld)))),
    length(Theory, Size),
    assert(spec(inputTheorySize(Size))).
    %nl, write_term_c('Complete initialising the input theory, signature and the preferred structure.'),nl.   % Get all sentences from both the theory and the preferred structure.


% only clear the internal assertions, not ones from the input theory, e.g., trueSet, falseSet..

specification:- retractall(spec(_)),
                maplist(assert, [spec(screenOutput(false)), % do not output solutions to screen.
                                spec(costLimit(50)),
                                spec(roundLimit(0)),
                                spec(proofStatus(0)),
                                spec(threshold(1)),
                                spec(roundNum(0))]).
supplyInput:-
    (\+trueSet(_)-> assert(trueSet([])),!;true),
    (\+falseSet(_)-> assert(falseSet([])),!;true),
    (\+heuristics(_)-> assert(heuristics([])),!;true),
    (\+protect(_)-> assert(protect([])),!;true).
/**********************************************************************************************
    precheckPS: check if the preferred structure is self-conflicting.
    Input: the assertions of trueSet([...]) and falseSet([...])
**********************************************************************************************/
precheckPS:-
    %nl,nl,write_term_c('-------Start the consistency check on the preferred structure--------'),nl,
    % no conflicts in the preferred structure
    spec(pft(Trues)),
    spec(pff(Falses)),
    % get the conflicts between the preferred structure and the constrain axioms in the thoery.
    findall(('Constraint', Constrain),
            (spec(protList(ProtectedList)),
             member(Constrain, ProtectedList),
             Constrain=[-_|_],
             notin(+_, Constrain),    % get a constraint axiom from the theory
             slRL(Constrain, Trues, [], [_|_], [], [])),    % Proof [_|_] exist which is not an empty list.
            Conflict),
    % C1: the propositions that occur in both the true set and the false set.
    findall(('Both sets', X), (member(X, Trues), member(X, Falses)), Conflicts1),
    % C2: equality/inequality conflicts in the true set.
    findall(('True set', X = Y, X\=Y),
            (member([+[=, X, Y]], Trues),
             (member([+[\=, X, Y]], Trues); member([+[\=, Y, X]], Trues))),
            Conflicts2),
    % C3: equality/inequality conflicts  in the false set.
    findall(('False Set', X = Y, X\=Y),
            (member([+[=, X, Y]], Falses),
             (member([+[\=, X, Y]], Falses); member([+[\=, Y, X]], Falses))),
            Conflicts3),
    findall((Reason, A), (member([+[\=, X, X]], Trues), A= (X \= X), Reason = 'True set';
                member([+[=, X, X]], Falses), A= (X = X), Reason = 'False set'),
            Conflicts4),
    appAll(append, [Conflict, Conflicts1, Conflicts2, Conflicts3], [Conflicts4], Conflicts, 1),
    checkPSPrint(Conflicts).


checkPSPrint([]):- !.% nl,write_term_c('-------Check finished. The preferred structure is consistent.').
checkPSPrint(Conflicts):-
    Conflicts \= [],
    nl,nl, write_term_c('-------Consistency check failed due to the following propositions:'),
    nl, write_term_All(Conflicts),
    nl, write_term_c('-------Please revise the preferred structure, Thanks.'),nl,nl.


initTheory(Axioms, Clauses):-
    findall(ClOut,
                (member(Axiom, Axioms),
                convertClause(Axiom, Cl),
                orderAxiom(Cl, ClOut)),
            TheoryRaw),
    sort(TheoryRaw, Clauses).

/**********************************************************************************************************************
    initSignature(Theory): based on the input theory in the original format, e.g., axiom([=(a,b)])
        Input:           Theory: clauses in the internal format.
        Output:        assert the signature information to global variable 'signature'.
                    To write_term_c it, please use: spec(signature(X)),write(X).
        Example: X = (X1, X2),
                 X1 = [(a, [(1, theory)], [[[diana]]]),  ((=), [(2, falseSet),  (2, theory)], [[[diana]], [[camilla]]]),  (vum, [(2, theory)], [[[camilla]], [[...]]]),  (women, [(1, theory)], [[]])]
                 X2 = [[camilla], [diana], [william]]
************************************************************************************************************************/
recSignature(Theory):-
    findall((Predicate, Arity, Args, theory),
            (member(Clause, Theory),
             (member(-Proposition, Clause);
              member(+Proposition, Clause)),
             Proposition = [Predicate| Args],
              length(Args, Arity)),
            S1),
    spec(pft(TrueSet)),
    spec(pff(FalseSet)),
    findall((Predicate, Arity, Args, Source),
            ((member([+Proposition], TrueSet), Source = trueSet;
              member([+Proposition], FalseSet), Source = falseSet),
             Proposition = [Predicate| Args],
              length(Args, Arity)),
            S2),
    append(S1, S2, S3),
    % Merge the arity and argument information of each predicate.
    % Meanwhile, rise error if one predicate is overloaded.
    mergeArity(S3, Sig, ConsAll),
    sort(ConsAll, Constants),          % remove duplicates.
    % Assert signature.
    assert(spec(signature(Sig, Constants))).

/**********************************************************************************************************************
mergeArity(InputSig, OutputSig, OutputCons): puts all arities information of a predicate into one element of the output list; output a list of constants.
Merge the triples of Input list which have the same first element.
Input: [(predicate1, 2, arguemnts, theory), (predicate2, 1,arguemnts2, theory), (predicate1, 1, arguemnts3, prefStruc), (predicate3, 4, arguemnts4, prefStruc)]
Output: [(predicate1, [(1, prefStruc),  (2, theory)], [[List of 1st arguments], [List of 2st arguments]...]),  (predicate2, [(1, theory)],  [[List of 1st arguments]]),  (predicate3, [(4, prefStruc)],  [[List of 1st arguments],..., [List of 4th arguments]])].
************************************************************************************************************************/
mergeArity([], [], []):- !.
mergeArity(SigTemp, [(Pred, Arities, ArgsDomains)| TMerged], ConsAll):-
    SigTemp = [(Pred, _, _, _) | T],
    % Get all the arities of predicate Pred.
    findall( (Arity,Source),
            member((Pred, Arity, _, Source), SigTemp),
            AritiesTemp),
    % Remove duplicates.
    sort(AritiesTemp, Arities),
    % Get all arguments information of Pred where variables are replace with [].
    findall( CArgs,
                (member((Pred, _, Arg, _), SigTemp),
                 % get all variables in the argument list.
                 findall(vble(X), member(vble(X), Arg), VbleList),
                 % replace each variable with [] in the argument list.
                 repList(VbleList, [], Arg, CArgs)),
                Cons),

    % Each sublist of ConsDomains is a list of constants which occur as the particular argument of that predicate.
    (transposeF(Cons, ConsTrans)-> !,
        % remove empties
        appEach(ConsTrans, [delete, []], ConsNonEmp),
        % remove duplicates
        appEach(ConsNonEmp, [sort], ArgsDomains),
        mergeAll(ArgsDomains, [], ConsList1),
        delete(T, (Pred, _, _, _), SigRest),
        mergeArity(SigRest, TMerged, ConsList2),
        append(ConsList1, ConsList2, ConsAll);
      % transposeF fails if the arity is not in same sizes.
        nl, write_term_c('---------- Error: Predicate is overloaded: ----------'), nl,
        write_term_c("The arities of "), write_term_c(Pred), write_term_c(" include "), write_term_c(Arities), nl,
          nl, write_term_c('Please correct it first.'), fail).


/**********************************************************************************************************************
        initProtList(Signature): assert the protected list including arity of each predicate in the preferred structure.
        input: [(black, [(1, prefStruc)], [lily,bruce]),  (white, [(1, prefStruc),  (1, theory)], [..]),  (swan, [(1, theory)], [..]),  (european, [(1, theory)], [..]),  (german, [(1, theory)], [..])].
************************************************************************************************************************/
initProtList:-
    % get the input of signature information.
    spec(signature(Signature, _)),
    (protect(X)-> ProList = X; ProList = []),                                      % Get input protected list.
    findall(Item,
            ( member(Item1, ProList),
              (is_list(Item1)->
                  convertClause(Item1, Item);
                  Item1 = Item)),
            Protected),

    % protect the arity of a predicate that is from the preferred structure.
    findall([arity(Predicate)],
               ( member((Predicate, ArityInfo, _), Signature),   % Get a predicate occur in the theory or preferred structure
                 member((_,Source), ArityInfo),
                 occur(Source, [trueSet, falseSet])),           % This predicate occur in the preferred structure.
            PPs),                                          % The set of arity of each predicate in preferred structure.

    % protect the predicate symbol that is from the preferred structure.
    findall([Predicate],
               ( member((Predicate, ArityInfo, _), Signature),   % Get a predicate occur in the theory or preferred structure
                 member((_, Source), ArityInfo),
                 occur(Source, [trueSet, falseSet])),      % This predicate is not from the input claus, so it occurs in the preferred structure.
            PPP),                                          % The set of arity of each predicate in preferred structure.
    append(Protected, PPs, P1),
    append(P1,PPP, ProtectedList),

    assert(spec(protList(ProtectedList))).

/**********************************************************************************************************************
    minimal(TheoryIn, EC, RsIn, Minimal, RsOut): find a minimal set of the input theory via Depth-first search.
        * also reset independent variables' serial number starting from 1.
    Input:      TheoryIn is a list of clauses.
        EC is the equivalence classes.
        RsIn is the current list of repair plans that has been applied.
    Output:     Minimal is the minimal set of TheoryIn that is found first.
                RsOut is the revised list of repair plans.
************************************************************************************************************************/
minimal([[]],_,_,[[]],_).
minimal([],_,_,[],_).
minimal(TheoryIn, EC, RsIn, Minimal, RsOut):-
    sort(TheoryIn, TheorySorted1),        % delete all duplicates.
    % prefer to keep rules, so put them after assertions.
    findall([+[P|Args]], member([+[P|Args]], TheorySorted1), Assertions),
    deleteAll(TheoryIn, Assertions, Rules),
    append(Assertions, Rules, TheorySorted),
    smaller(TheorySorted,  EC, RsIn, [], MinimalTem, RsOut),
    resetIndepVble(TheoryIn, Minimal).

smaller(TheorySorted,  _, RsIn, [], TheorySorted, RsIn).
/**********************************************************************************************************************
    smaller(TheoryIn, EC, RsIn, Axioms, Minimal, RsOut):
    Input:      TheoryIn is a list of clauses.
        EC is the equivalence classes.
        RsIn is the current list of repair plans that has been applied
    Intermediate: Axioms is a list of axioms found.
    Output:     Minimal is the minimal set of TheoryIn that is found first.
                RsOut is the revised repair plans.
smaller([[+[bird, [polly]]], [+[penguin, [tweety]]], [+[bird, vble(y)], -[penguin, vble(y)]], [+[feather, vble(y)], -[bird, vble(y)]], [+[fly, vble(x)], -[bird, vble(x)]]], [[[polly]], [[tweety]]], [], [], _93064, []).

smaller([], _, Rs, Minimal, Minimal, Rs).
% Cl is a theorem rather than an axiom.
smaller([Cl| ClRest], EC, RsIn, Axioms, Minimal, RsOut):- pause,
    negateCl(Cl, Goal),
    append(Axioms, ClRest, TheoryTem),    % Get the candidates of the minimal set.
    slRL(Goal, TheoryTem, EC, [_|_],_,_), !,  % Goal is a theorem of the rest clauses in the theory. Do not continue to try the next branch of smaller/6.
    delete(RsIn, expand(Cl), RsNew),    % If Cl is added by a repair plan, reject that repair plan.
    smaller(ClRest, EC, RsNew, Axioms, Minimal, RsOut).

% Cl is an axiom, record it and then examine the next clause.
smaller([Cl| ClRest], EC, RsIn, Axioms, Minimal, RsOut):-pause,
    smaller(ClRest, EC, RsIn, [Cl| Axioms], Minimal, RsOut).
    ************************************************************************************************************************/


/**********************************************************************************************
    resetIndepVble(TheoryIn, TheoryOut):
    Input: a list of axioms.
    Output: a list of axioms where independent variables' serial numbers start from 1.
    * Update protected list!
**********************************************************************************************/
resetIndepVble(TheoryIn, TheoryOut):-
    findall([V, Num],
                (   % get arguments in axioms.
                    (member(Cl, TheoryIn),
                    (member(+[_|Args], Cl); member(-[_|Args], Cl))),
                    member(vble(V), Args),
                    atom_concat(iv, AtomNum, V),
                    atom_number(AtomNum, Num)),
            InVInfoTem),
    sort(InVInfoTem, InVInfo), % remove duplicates.
    transposeF(InVInfo, [OldInVbleList, SerialNums]),
    length(SerialNums, TotalNum), % Get the total number of serial numbers,
    adverseEnum(TotalNum, ResetSerials),
    findall((vble(OldInVble), vble(NewInVble)),
            (nth1(I, OldInVbleList, OldInVble),        % OldInVble is the Ith proposition in OldInVbleList.
             nth1(I, ResetSerials, SNum),
             atom_concat(iv, SNum, NewInVble)),
            RenameList),
    appEach(TheoryIn, [appEach, [appLiteral, [replace, 1, RenameList]]], TheoryOut).
