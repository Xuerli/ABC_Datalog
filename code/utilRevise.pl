/*
Date: 25 Feb 2019
*/


:-[util].

/*
indepPoorfs([Proof1|PRest], Proof2, IndepSetsIn, Out):-
    findall([(IndProofs, ClSet), (IndProofs, ClSet), 
                (member((IndProofs, ClSet),IndepSetsIn),
                 findall(Clause, member((_,Clause,_,_,_), Proof1), S1),
                 intersection(S1, ClSet
                        notin(Clause, ClSet))),
                 IndPNew = [Proof1| IndProofs],
                 append(ClSet, ClSetNew)
            IndepPairs),
    */
/*
costRepairs (R, C): calculate the cost C by split R into members one by one.
costRepair （_, _, C）:C is 0 when (R, _) is a member of Rs, otherwise C is 1.
*/
% if a name was already split, then additional splits to the same name are free
costRepairs([], 0) :- !.
costRepairs([R|Rs], C) :- costRepair(R, Rs, C1), costRepairs(Rs, C2), C is C1 + C2.

costRepair((R, _), Rs, 0) :- member((R, _), Rs), !.
costRepair(_, _, 1).

/**********************************************************************************************************************
    strDominated(FNum1, FNum2): Theory2 is strictly dominated by Theory1.
        Input:     FNum1: the list of Theory1's fault numbers.
                FNum2: the list of Theory2's fault numbers.
************************************************************************************************************************/
strDominated(FNum1, FNum2):-
    sd0(FNum1, false, FNum2).
% success only when all F2 >= F1 among which exist one F2>F1.
sd0([], Flag, []):- Flag.
sd0([F1|_], _, [F2|_]):- F1 > F2, fail,!.
sd0([F1|T1], Flag, [F2|T2]):- F1 = F2, !, sd0(T1, Flag, T2).
sd0([F1|T1], _, [F2|T2]):- F1 < F2, !, sd0(T1, true, T2).



/**********************************************************************************************************************
    termOcc(LF, Theory, OccF): count term F's occurances in the theory
        Input:  F: a constant/predicate;
                Theory: a list of axioms
        Output: OccF: the number of F's occurances in Theory.
************************************************************************************************************************/
termOcc(F, Theory, OccF):-
    cterm(F, Theory, 0, OccF).
cterm(_, [], Num, Num):-!.
cterm(F, [Axiom| RestAxioms], NumIn, NumOut):-
    findall(Prop, (member(+Prop, Axiom); member(-Prop, Axiom)),
            AllProp),
    flatten(AllProp, Props),
    delete(Props, F, PRest),
    length(Props, L1),
    length(PRest, L2),
    NumNew is L1 - L2 + NumIn,
    cterm(F, RestAxioms, NumNew, NumOut).

/**********************************************************************************************************************
    quicksort(List,Sorted):    quick sort by value for a list of pairs (value, repair)
        Input:  List
        Output: Sorted
************************************************************************************************************************/
quicksort(List,Sorted):-q_sort(List,[],Sorted).
q_sort([],Acc,Acc) :- !.
q_sort([H|T],Acc,Sorted):-
  pivoting(H,T,L1,L2),
  q_sort(L1,Acc,Sorted1),
  q_sort(L2,[H|Sorted1],Sorted).

pivoting(_,[],[],[]) :- !.
pivoting(((H1,H2),Vh),[((X1,X2),Vx)|T],[((X1,X2),Vx)|L],G):- (X1>H1; X1=H1,X2=<H2),  pivoting(((H1,H2),Vh),T,L,G), !.
pivoting(((H1,H2),Vh),[((X1,X2),Vx)|T],L,[((X1,X2),Vx)|G]):- pivoting(((H1,H2),Vh),T,L,G).

pivoting((H1,A1,B1),[(H2,A2,B2)|T],[(H2,A2,B2)|L],G):- !,
    number(H1), number(H2),
    H2=<H1,  pivoting((H1,A1,B1),T,L,G).
pivoting((H1,A1,B1),[(H2,A2,B2)|T],L,[(H2,A2,B2)|G]):- pivoting((H1,A1,B1),T,L,G).



/**********************************************************************************************************************
        dummyTerm(Term, ClP, TheoryIn, DummyTOut):
            generate the Dummy term.
        Input:  Term, e.g., mum.
                TheoryIn: the input theory.
                After renaming Term to DummyTOut in its clause CL1, the unification between CL1 and ClP is broken.
        Output: DummyTOut the dummy term, e.g., dummy_mum_2
************************************************************************************************************************/
dummyTerm([Term], TheoryIn, [DummyTOut]):- !,
    dummyTerm(Term, TheoryIn, DummyTOut).

dummyTerm(Term, TheoryIn, DummyTOut):-
    % if the term is already dummy, e.g., dummy_mum_2, get the original term
    (atom_concat(dummy_, Term0, Term)->                % Term0: mum_2
        atom_concat(TermOrig, STail, Term0),         % STail = _2, TermOrig = mum
        atom_chars(STail, ['_'|SerStr]),        
        term_string(SNum, SerStr), !;            % Ser = '2' 
        TermOrig = Term, SNum = 0), 
    atom_concat(dummy_, TermOrig, DummyTerm1),
    term_string(DummyTerm1, NameString),
    string_concat(NameString, "_", NamePre),
    
    findall(Prop, (    member(Axiom, TheoryIn),
                    (member(+Prop, Axiom);
                     member(-Prop, Axiom))),
            AllProp),
    flatten(AllProp, AllF1),    % the list of all predicate symbol and constant
    sort(AllF1, AllF), 
    findall([Num, Cand], (    member(T, AllF),
                        term_string(T, String),
                        %sub_string(String,_,_,_,NamePre),    % the name prefix is contained by the string.
                        split_string(String,"_", "dummy_", [StrTermOrig, NumLast]), %split_string("dummy_load2_2", "_", "", X).X = ["dummy", "load2", "2"].
                        term_string(TermOrig, StrTermOrig),
                        term_string(Num, NumLast),
                        number(NumLast),
                        (Num > SNum-> Cand = T, !; Cand =[])),
            DummyPairs),
    (DummyPairs = [] ->
        string_concat(NamePre, "1", DummyTstr),
        term_string(DummyTOut, DummyTstr), !;
    % heuristics, the smaller the serial number is, the more likely an individual belongs to. 
    % so start with assignming the smallest serial number which bigger than Term.
     DummyPairs = [_|_]-> 
         sort(DummyPairs, PSorted),
         transposeF(PSorted,[_,X]),
         (X = [DummyTOut|_], !;     % fails when the input term has the largest serial number.
         NewNum is SNum +1,
         term_string(NewNum, NewNumStr),
         string_concat('_', NewNumStr, NewTail),
         string_concat(NameString, NewTail, DummyTStr),
         term_string(DummyTOut, DummyTStr))).

% FirstNum([97, 97, 97, 49, 49, 50, 51], '1123'). Get the serial number.
firstNum([], _):- fail, !.
firstNum([H|T], SerNum):- 47<H, H<58, atom_codes(SerNum,[H|T]), !.
firstNum([_|T], SerNum):- firstNum(T, SerNum).            % H is a number.

/*********************************************************************************************************************************
    general(ClauseIn, ClauseOut, ReSubs): Generalise the axiom by replace the constant which occur more than once with a variable.
    Input:  ClauseIn: the clause to be generalised.
    Output: ClauseOut: the gneralised Clause which has no constant that occurs more than once.
            ReSubs: the substitution satisfies: ClauseOut* ReSubs = ClauseIn
**********************************************************************************************************************************/
generalise([], []):- !.
generalise(ClauseIn, ClauseOut):-
    generalise(ClauseIn, ClauseOut, _, _).
generalise(ClauseIn, ClauseOut, Cons2Vbles, ReSubs):-
    % get the list of link constants which occur both in the head and the body.
    findall(Constant,
            (member(+[_| ArgHead], ClauseIn),
             member(Constant, ArgHead),
             member(-[_| ArgBody], ClauseIn),
             member(Constant, ArgBody)),
            Cons1),
    % get the list of constants which occur at least twice in the body.
    findall(Constant,
            (member(-[P1| ArgB1], ClauseIn),
             member(-[P2| ArgB2], ClauseIn),
             [P1| ArgB1] \= [P2| ArgB2],
             member(Constant, ArgB1),
             member(Constant, ArgB2)),
            Cons2),
    % get the list of variables in the input clause.
    findall(X,
            ( (member(+[P1| Arg], ClauseIn);
               member(-[P2| Arg], ClauseIn)),
              member(vble(X), Arg)),
            AvoidList),
    % combine all constant candidates and remove the duplicates by sort them.
    append(Cons1, Cons2, Cons),
    sort(Cons, ConsList),
    getNewVble(ConsList, AvoidList, Cons2Vbles, ReSubs),
    appEach(ClauseIn, [appLiteral, [replaceS, 1, Cons2Vbles]],  ClauseOut).
/*
% Get substitutions of a new variable for each constant in ConsList
% and the new variable should not occur in the AvoidList.
getNewVble([[c]], [vble(z),vble(x)], NewVbleSub, ReSubs).
NewVbleSub = [([c], vble(z))],
ReSubs = [[c]/vble(z)].
*/
getNewVble(ConsList, AvoidList, NewVbleSub, ReSubs):-
    char_code(z, Zcode),
    getNewVble(ConsList, AvoidList, Zcode, NewVbleSub, ReSubs).

getNewVble([], _, _, [], []):-!.
% Get one valid new variable with ascii code : Code.
getNewVble([C| CRest], AvoidList, Code, [(C, vble(Char))| RestVbleSub], [C/vble(Char)| ReSubs]):-
    char_code(Char, Code),
    notin(Char, AvoidList),        % the new variable is Char iff it is not one of the list of variables.
    NextCode is Code - 1, !,
    getNewVble(CRest, AvoidList, NextCode, RestVbleSub, ReSubs).
% If the char of Code is already in the variable list, then try the one before it on ascii table.
getNewVble(ConsList, AvoidList, Code, NewVbleSub, ReSubs):-
    NewCode is Code -1,
    getNewVble(ConsList, AvoidList, NewCode, NewVbleSub, ReSubs).

/**********************************************************************************************************************
    rewriteVble(Goals, InputClause, ClNew, AllSubs):
            rewrite the variables in InputClause which occur in the Goals.
    Input: Goals: a list of sub-goals.
           Anc: the derivation of Goals from the original goal.
           InputClause: the input clause which will be used to resolve the left most subgoal in Goals.
    Output: ClNew: the rewritten clause.
            AllSubs: the substitutions of from the input goals to the output goals.
************************************************************************************************************************/
% REW1: when there is no goal nor input clause, return.
rewriteVble([], Cl, Cl, []):- !.
rewriteVble(_, [], [], []):- !.

% REW2: when there is shared variable, rewriting is needed.
rewriteVble(Goals, InputClause, ClNew, AllSubs):-
    % generate substitutions which replace old variable vble(X) with its new name vble(NewX).
    findall(vble(NewX)/vble(X),
            (member(-[_|Args], Goals),
             member(vble(X), Args),
             member(Literal, InputClause),
             ( Literal = -[_| ArgsInCl];
               Literal = +[_| ArgsInCl]),
             % If the variable vble(X) occur in ArgsInCl, rename it with vble(NewX).
             newVble(vble(X), ArgsInCl, vble(NewX))),
            AllSubsTem),
     sort(AllSubsTem, AllSubs),
     subst(AllSubs, InputClause, ClNew).    % GoalsNew == Goals when AllSubs = [].

/*
maxMach(Arg1, Arg2):
maxMach([a,b,d,e],[a,d,d],X).
X = [[0], [], [1, 2], []].
*/
maxMach([],_,[]).
maxMach([H| T], Arg2, [MatchIndexes| Rest]):-
    findall(Pos, nth0(Pos, Arg2, H), MatchIndexes),
    maxMach(T, Arg2, Rest).
    
/*****************************************************************************************************************    
    essSubs(Suffs, Rule, SubsList):-
        get the substitutions of Rule if it is involved in all proofs of a preferred proposition.
    Input:     Suffs: a list of sufficiencies.
            Rule: a rule.
    Outpt:    SubsList: a list of substitutions [Subs1, Subs2,...] 
                        where Subs1 is the substitutions applied to Rule in a proof.
****************************************************************************************************************/
essSubs([], _, []).

% if there is one proof which does not contain Rule, then Rule is not essential for this sufficiency. 
essSubs([(_,Proofs)|Rest], Rule, SubsOut):-
    setof(Proof, (member(Proof, Proofs), 
                   notin((_,Rule,_,_,_), Proof)),
             [_|_]), !,
    essSubs(Rest, Rule, SubsOut).        % continue checking the next.
% Otherwise, record the substitutions of Rule in these proofs where it is essential.
essSubs([(_,Proofs)|Rest], Rule, SubsOut):-
    findall(Subs, (    member(Proof, Proofs), 
                     member((_,Rule,Subs,_,_), Proof)),
             AllSubs), 
    essSubs(Rest, Rule, SubsRest),        % continue checking the next.
    append(AllSubs, SubsRest, SubsOut).    

/*    
notEss2suff(Suffs, Rule, GroundHead/Subs):-
    success if there is no preferred proposition whose proofs all instantiate Rule's head as GroundHead or by Subs.
*/
notEss2suff([], _, _).
notEss2suff([(_,Proofs)|Rest], Rule, Subs):-
    forall(    member(Proof, Proofs), 
             member((_,Rule,Subs,_,_), Proof)), !,
    fail; 
    notEss2suff(Rest, Rule, Subs).


/*
notEss2suffG([], _, _).
notEss2suffG([(_,Proofs)|Rest], Rule, GroundHead):-
    Rule = [+HeadProp|_],
    forall(member(Proof, Proofs), 
                 (member((_,Rule,Subs,_,_), Proof), 
                 subst(Subs, HeadProp, GroundHead))), !,
    fail; 
    notEss2suffG(Rest, Rule, GroundHead).
    
notEss2suff(Suffs, Axiom):-
    success if there is no preferred proposition whose proofs all contain the Axiom.
*/
notEss2suff([], _).
notEss2suff([(_,Proofs)|Rest], Axiom):-
    forall(member(Proof, Proofs), member((_,Axiom,_,_,_), Proof)), 
    !, fail; 
    notEss2suff(Rest, Axiom).

% When vble(X) occur in the argument list Args, rename it with a new name which does not occur in Args.
newVble(vble(X), Args, vble(NewX)):-
    member(vble(X), Args),
    string_concat(X,'1',Y),
    term_string(Term, Y),
    (notin(vble(Term), Args)->NewX = Term, !;
     newVble(vble(Term), Args, vble(NewX))).


/**********************************************************************************************************************
        removeDups(ListIn, ListOut): removes duplicates from a sorted list
        Input:  ListIn
        Output: ListOut
    Example: removeDups([1,2,4,2,4,5],X). X = [1, 2, 4, 5].
************************************************************************************************************************/
removeDups([],[]) :- !.
removeDups([A|R],T) :- member(A,R), !, removeDups(R,T).         % if A exists in remainder, then omit it
removeDups([A|R],[A|T]) :- \+(member(A,R)), removeDups(R,T).    % A is a non-duplicate member, which is retained in the output list.

% Assertion protect check
asserProCheck([_|_],_):- !. % for rules, pass.
asserProCheck([+[P|_]], ProtectedList):- 
    notin(asst(P), ProtectedList).

/**********************************************************************************************************************
        upRsBanned(RsBIn, RP, RsBOut): update banned list of repairs based on the current repair plan.
        Input:  RsBIn : the list of previous banned repairs.
                RP: input the current repair plan.
        Output: RsBOut: the list of updated banned repairs.
************************************************************************************************************************/

upRsBanned(RsBIn, [RP|Rest], Out):- upRsBanned(RsBIn, RP, Tem), !, upRsBanned(Tem, Rest, Out).
upRsBanned(RsBIn, add_pre(Pre, Rule), [dele_pre(Pre, Rule)| RsBIn]):- !.
upRsBanned(RsBIn, dele_pre(Pre, Rule), [add_pre(Pre, Rule)| RsBIn]):- !.
upRsBanned(RsBIn, expand(Clause), [delete(Clause)| RsBIn]):- !.
upRsBanned(RsBIn, delete(Clause), [expand(Clause)| RsBIn]):- !.
upRsBanned(RsBIn, remove_n(P,N, L1), [add_n(P, N, L1)| RsBIn]):- !.
upRsBanned(RsBIn, add_n(P, N, L1), [remove_n(P,N, L1)| RsBIn]):- !.
upRsBanned(RsBIn, analogy(_, RruleNew), [delete(RruleNew)| RsBIn]):- !.
upRsBanned(RsBIn, ass2rule(_, RruleNew), [delete(RruleNew)| RsBIn]):- !.
%upRsBanned(RsBIn, merge(F1, F2), [rename(F2)| RsBIn]):- !.
upRsBanned(RsBIn, ass2rule(_, RruleNew), [delete(RruleNew)| RsBIn]):- !.
upRsBanned(RsB, _, RsB):- !.


revertFormRep(dele_pre(-Pre, RuleIn), dele_pre(-PreA, RuleOut)):- !,
    revert(Pre, PreA),
    appEach(RuleIn, [appLiteral,  revert], RuleOut).

revertFormRep(add_pre(-Pre, RuleIn), add_pre(-PreA, RuleOut)):- !,
    revert(Pre, PreA),
    appEach(RuleIn, [appLiteral,  revert], RuleOut).

revertFormRep(delete(Clause), delete(ClauseOut)):- !,
    appEach(Clause, [appLiteral,  revert], ClauseOut).

revertFormRep(expand(Clause), expand(ClauseOut)):- !,
    appEach(Clause, [appLiteral,  revert], ClauseOut).

revertFormRep(analogy(R1, R2), analogy(R1Out, R2Out)):- !,
    appEach([R1, R2], [appEach, [appLiteral,  revert]], [R1Out, R2Out]).

revertFormRep(ass2rule(R1, R2), ass2rule(R1Out, R2Out)):- !,
    appEach([R1, R2], [appEach, [appLiteral,  revert]], [R1Out, R2Out]).

revertFormRep(X,X).
/**********************************************************************************************
    empty(X, Y):- flatten empty list, e.g., empty([[[]], [[]],[]], []);empty([a,[]],[a, []])
       input: X is a list
       output: Y is [] if X is a list of empty lists.
***********************************************************************************************/
empty(X, []):- flatten(X,[]),!.
empty(X, X):- \+flatten(X,[]).
/**********************************************************************************************
   based on transpose from clpfd: https://github.com/SWI-Prolog/swipl-devel/blob/master/library/clp/clpfd.pl#L6371
   Input: Ls is a list of lists.
   Output: Out is the transposition of Ls, where the sublist of empty lists, e.g. [[],[],[[]]] is flatten as [].
***********************************************************************************************/
transposeF([], Out):- 
     maplist(=([]), Out), !.
transposeF(Ls, Out):-
        must_be(list(list), Ls),
        lists_transpose(Ls, Ts),
        appEach(Ts, [empty], TS1),
        appEach(TS1,[delete, []], Out).    % flatten the list of empty lists as [].

lists_transpose([], []).
lists_transpose([L|Ls], Ts) :-
        maplist(same_length(L), Ls),
        foldl(transpose_, L, Ts, [L|Ls], _).

transpose_(_, Fs, Lists0, Lists) :-
        maplist(list_first_rest, Lists0, Fs, Lists).

list_first_rest([L|Ls], L, Ls).
