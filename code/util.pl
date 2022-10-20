/*
  This file contains the basic functions/predicates that assist other ABC system's functions.
  Update Date: 13.08.2022
*/

/*********************************************************************************************************************************
    allTheoremsC(ABox, Constant, Theorems): get all theorems whose arguments include the targeted constant.
    * Inequality only between constants at the same position in arguments of predicates.
    Input:  ABox: the ABox of the KG.
            EC: the equivalence class.
            Constant: the targeted constant, e.g., [c].
    Output: Theorems is a list of theorem whose argument contains the constant.
**********************************************************************************************************************************/
allTheoremsC(Abox, C, Theorems):-    % all theorems whose arguemnts contain C1
  findall([+[P| Args]], (member([+[P| Args]], Abox), member(C, Args)),
        Theorems).

% get all theorems that contain predicate P.
allTheoremsP(Abox, P, Theorems):-    % all theorems whose arguemnts contain C1
  findall([+[P| Args]], member([+[P| Args]], Abox),
        Theorems).
/**********************************************************************************************
    appAll(Predicate, List, ArgumentList, nth, Output):
        apply the predicate to one element in the List.
        * The output has to be the last argument of the Predicate.
        and take its output as the nth (n > 0) input argument for the next calculation.
        Count from 0, so if arity(Predicate) = M, then max(N) = M-1.
        Output is resulted by applying all elements in the list.
        * e.g., appAll(append, [[1],[2],[3]], [[5]], X, 1), X = [3, 2, 1, 5].
        * e.g., appAll(sum, [1,2,3], [5], Y, 1). Y = 5+1+2+3 = 11
***********************************************************************************************/
appAll(_, [], [Out], Out, _):-!.
appAll(_, [], ArgsNew, Out, _):-!,
    last(ArgsNew, Out).
appAll(Predicate, [H| T], Args, Output, N):- !,
    append([Predicate, H], Args, E1),
    append(E1, [Out], EList),
    Expression =..EList,
    call(Expression),
    Pos is N-1,     % the first input is the element in the list
    replacePos(Pos, Args, Out, ArgsNew),    % replace the Pos element in Args with Out resulting ArgsNew
    appAll(Predicate, T, ArgsNew, Output, N).


/**********************************************************************************************
    appEach(List, [Predicate, ExtraArgu1, ExtraArgu2,..], OutputList):
        apply the predicate to each element in the List and other arguments in ArgumentList.
        appEach/2 succeed when all expressions succeed.
        appEach/3, appEach/4 succeed when at least one expression is succeed.
    Input:     Predicate: the predicate to call
            List: each of elements in List will be the first argument when call Predicate.
            ExtraArgusList: a list of the other arguments for Predicate.
                            If artiy of Predicate is 1, then ExtraArgusList = [].
    Output:    OutputList is a list of each output.
    * The length of Output is same with List, which is the nth(Output) = Predicate(nth(List), Argument).
    * e.g., appEach([[1],[2],[3]], [append, [5]], X), X = [[1, 5], [2, 5], [3, 5]].
    * e.g., appEach([1,2,3], [sum, 5], Y). Y = [6, 7, 8]
***********************************************************************************************/
% Args is the list of extra arguments.
appEach([], _):- !.
appEach([H| T], [Predicate| Args]):- !,
    append([Predicate, H], Args, EList),
    Expression =..EList,
    call(Expression),
    appEach(T, [Predicate| Args]).

appEach([], _, []):- !.
appEach([H| T], [Predicate| Args], Output):- !,
    append([Predicate, H], Args, E1),
    append(E1, [HOut], EList),
    Expression =..EList,
    (call(Expression)-> Output = [HOut| TOut], !;
    \+call(Expression)-> Output = TOut,
    writeLog([nl,write_term('--Failed to apply '),nl,write_term(Expression),nl,  finishLog])),
    appEach(T, [Predicate| Args], TOut).

/**********************************************************************************************
    appLiteral(Literal, [Predicate, N, ExtraArgs1， ExtraArgs2...], OutLiteral):
        get Output by apply the predicate to the proposition in Literal
        along with other arguments in ExtraArgsList, except the last argument with +/-.
        The last argument with +/-, which will be assigned to OutLiteral.
    Input: N(counting from 0): the position of the proposition in the arguments of Predicate.
    appLiteral is similar to the predicate appEach/4.
***********************************************************************************************/
appLiteral(+Prop, Func):- !,
    appProp(Prop, Func).
appLiteral(-Prop, Func):- !,
    appProp(Prop, Func).
appLiteral(+Prop, Func, +PropNew):- !,
    appProp(Prop, Func, PropNew).
appLiteral(-Prop, Func, -PropNew):- !,
    appProp(Prop, Func, PropNew).


appProp(Prop, [Predicate| [N| ExtraArgs]]):-
    split_at(N, ExtraArgs,  ArgsFront, ArgsBack),
    append([Predicate| ArgsFront], [Prop| ArgsBack], EList),
    Expression =..EList,
    call(Expression).

appProp(Prop, [Predicate| [N| ExtraArgs]], PropNew):-
    number(N), !,
    split_at(N, ExtraArgs,  ArgsFront, ArgsBack),!,
    append([Predicate| ArgsFront], [Prop| ArgsBack], E1),
    append(E1, [PropNew], EList),
    Expression =..EList,
    call(Expression).

appProp(Prop, Predicate, PropNew):- !,
    Expression =..[Predicate, Prop, PropNew],
    call(Expression).


/***********************************************************************************************
     argsMis(Args1, Args2, Mismatches): get the mismatches which make Args1 ununifies Args2.
    Input:    Args1: a list of arguments, e.g., [[a], vble(x),[d], vble(x)]
             Args2: another arguments: e.g., [[a], [c], [d], [d]]
    Output: MisPairs: the list of mismatched constants between Args1 and Args2
            MisPairPos: the positions of these mismatched constants
    Example:argsMis([[a], vble(x),[d], vble(x) ],[[e], [c], [d], [d]], X, Y),
            X = [([a], [e]),  ([c], [d])],
            Y = [[([a], [e])], [], [], [([c], [d])]].
**********************************************************************************************/
argsMis([], [], [], []):- !.
argsMis([A1| Args1], [A2| Args2], MisPairs, [MisPair1| MisPos2]):-
    argPairMis(A1, A2, Sigma, MisPair1),
    subst(Sigma, Args1, ArgsSb1),
    subst(Sigma, Args2, ArgsSb2),
    argsMis(ArgsSb1, ArgsSb2, MisPairs2, MisPos2),
    append(MisPair1, MisPairs2, MisPairs).

argPairMis(C, C, [],[]):- !.
argPairMis([Cons], vble(X), [Cons]/vble(X), []):- !.
argPairMis(vble(X), [Cons], [Cons]/vble(X), []):- !.
argPairMis(vble(X), vble(Y), vble(X)/ vble(Y), []):-!.
argPairMis([Cons1], [Cons2], [], [([Cons1], [Cons2])]):-
    Cons1 \= Cons2.

% In datalog, an argument is either a constant, e.g., [c] or a variable, e.g., vble(v).
is_cons(X):- X = [Y], atomic(Y).
arg(X):- is_cons(X); X = vble(_).

% Assertion protect check
asserProCheck([_|_],_):- !. % for rules, pass.
asserProCheck([+[P|_]], ProtectedList):-
    notin(asst(P), ProtectedList).

/***********************************************************************************************
 compos1(Sub,SublistIn,SublistOut):
     SublistOut is the result of composing singleton substitution Subst with substitution SublistIn.
    compose1([bruce]/vble(x), [vble(x)/vble(y),[bruce]/vble(y)],X).
    X = [[bruce]/vble(x), [bruce]/vble(y)].

 Built in compose predicate fails when the second input is [], which is unwanted.
    compose(vble(x)/[bruce], [],X).   %     false.
**********************************************************************************************/
compose1([], SublistIn, SublistIn) :- !.
compose1(Sub, SublistIn, SublistOut) :-     % Append new substitution
    subst(Sub, SublistIn, SublistMid),        % after applying it to the old one
    (Sub = [_]-> append(Sub, SublistMid, SubTem);
     Sub = _/_-> SubTem = [Sub|SublistMid]),
    sort(SubTem, SublistOut).     % remove duplicates.

/**********************************************************************************************
    deleteAll(ListsInput, ListDel, ListOut) let the following true:
    ListOut = ListsInput - ListDel
**********************************************************************************************/
deleteAll([], _, []):-!.
deleteAll(ListsInput, [], ListsInput):-!.
deleteAll(ListsInput, [H|T], ListOut):-
    delete(ListsInput, H, ListRest),
    deleteAll(ListRest, T, ListOut).

% succeed if ArgsG and ArgsT can be unified by ignoring the tail of the longer argument list.
diff(ArgsG, ArgsT, ArgsTail):-
    length(ArgsG, LG),
    length(ArgsT, LT),
    (LG = LT-> ArgsTail = [], !,
        unification(ArgsG, ArgsT,_,[],_,_,[]);
    LG > LT-> split_at(LT, ArgsG, GFront, ArgsTail), !,
        unification(GFront, ArgsT,_,[],_,_,[]);
    LT > LG-> split_at(LG, ArgsT, TFront, ArgsTail),
        unification(ArgsG, TFront,_,[],_,_,[])).

% drop the last element from the input list
dropTail(ListIn, ListOut):-
length(ListIn, L), M is L-1,
split_at(M, ListIn, ListOut, _).



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

/**********************************************************************************************
    empty(X, Y):- flatten empty list, e.g., empty([[[]], [[]],[]], []);empty([a,[]],[a, []])
       input: X is a list
       output: Y is [] if X is a list of empty lists.
***********************************************************************************************/
empty(X, []):- flatten(X,[]),!.
empty(X, X):- \+flatten(X,[]).


fileName(FileCore, Function, Name):-
   date(date(_,X,Y)),
   get_time(Stamp),
   stamp_date_time(Stamp, DateTime, local),
   date_time_value(time, DateTime, time(H,M,_)),
   appEach([X,Y,H,M], [term_string], [X1,Y1,H1,M1]),
   string_concat(Y1,X1,Date),
   string_concat(H1,M1,Time),
   appEach([Date, Time], [string_concat, '_'], [Date1, Time1]),
   appAll(string_concat, ['.txt',Time1, Date1,'_' , FileCore , '_' , Function, 'log/'],[''], Name, 1).

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


/**********************************************************************************************
   gensymVble(N, ListOut):
   Input: N is the length of the independent variables list.
   Output: ListOut is the list of independent variables generated by gensym/2.
   * An independent variable starts with iv.
   Example: gensymVble(3,X).  X = [vble(iv6), vble(iv7)|vble(iv8)].
**********************************************************************************************/
gensymVble(1, vble(Exp)):- gensym(iv, Exp), !.
gensymVble(N, [vble(H)|T]):- gensym(iv, H), M is N-1, gensymVble(M, T).

/**********************************************************************************************************************
   init(Files, Vabs): read files to parameters and setup logs.
   Input:  Files: the files to read.
   Output:    Vabs: record files' content.
***********************************************************************************************************************/
init(FileList, Variables):-
    readInputs(FileList, Variables).

init(FileList, Variables, HeurPath):-
    init(FileList, Variables),
    open(HeurPath, read, StrInp),
    readFile(StrInp, Inp),       % the input abox is a list
    delete(Inp, end_of_file, InpData),
    close(StrInp),
    InpData = [Hur, ProtectedList, _, RsBanned, RsList, _],
    maplist(assert, [spec(heuris(Hur)), % do not output solutions to screen.
                     spec(protList(ProtectedList)),
                     spec(rsb(RsBanned)),
                     spec(rsa(RsList))]).

/**********************************************************************************************
   mergeTailSort(ListsInput, ListOut): combine all the tails without duplicates for a head in a list.
   * the output list is sorted based on the head of each eleme
   ListsInput = [(2,d),(1,a),(1,a),(4,d),(1,t)]
   ListOut = [(1, [a, t]),  (2, [d]),  (4, [d])].
**********************************************************************************************/
mergeTailSort([], []):- !.
mergeTailSort(ListsInput, ListOut):-
   mTail(ListsInput, [], ListTem),
   sort(ListTem, ListOut).
mTail([], ListOut, ListOut):-!.
mTail(ListIn, ListTem, ListOut):-
   ListIn = [(X,_)| TList],
   (member((X, _), ListTem)->
       % if the head has been recorded, continue to the next pair.
       mTail(TList, ListTem, ListOut);
       % otherwise, find the list of all the tails without duplicates for the head X.
       setof(Y1, member((X,Y1), ListIn), YS),
       ListTem2 = [(X, YS)| ListTem],
       sort(ListTem2, ListTem3),
       mTail(TList, ListTem3, ListOut)).


/**********************************************************************************************************************
   orderAxiom(ClIn, ClOut): then order the literals in a clause
   1. the head of the clause will be in the front of it.
   2. the equalities/inequalities literals will be the end of its body.
   3. the equalities will be in front of the inequalities.
   * the order is for the reduce the search space of sl resolution.
************************************************************************************************************************/
orderAxiom(ClIn, ClOut):-
   findall(-[=|Arg], member(-[=|Arg], ClIn), Eq),
   findall(-[\=|Arg], member(-[\=|Arg], ClIn), InEq),
   subtract(ClIn, Eq, A1),
   subtract(A1, InEq, A2),
   (notin(+_, A2)->    % A2 has no + literal
       append(A2, Eq, A4),
       append(A4, InEq, ClOut);
   member(+Head, A2)->
       subtract(A2, [+Head], A3),
       append(A3, Eq, A4),
       append(A4, InEq, A5),
       append([+Head], A5, ClOut)).

/**********************************************************************************************************************
    check existances.
***********************************************************************************************************************/

notin(_, List):- \+is_list(List), nl,print('ERROR: '), pause, print(List), print(' is not a list'),nl,fail,!.
notin(X, List):- \+member(X, List), !.

notEss2suff([], _).
notEss2suff([(_,Proofs)|Rest], Axiom):-
    forall(member(Proof, Proofs), member((_,Axiom,_,_,_), Proof)),
    !, fail;
    notEss2suff(Rest, Axiom).


occur(_, List):- \+is_list(List), nl,print('ERROR: '), print(List), print(' is not a list'),nl, fail,!.
occur(X, List):- member(X, List), !.    % avoid redo member(_, List) where '_' is assigned values


/**********************************************************************************************
    orphanVb: check if there is orhpan variable in the input theory
    Input: an axiom
    Output: The axiom and the orphans if there are orphan variables, otherwise, [].
**********************************************************************************************/
orphanVb([], []):- !.
orphanVb(Axiom,  OpVbles):-
    member(+[_| ArgsHead], Axiom),
    findall(vble(X), (member(-[_| ArgsBody], Axiom), member(vble(X), ArgsBody)), BodyVbles),
    % exists orphan variables.
    setof(vble(X),
            (member(vble(X), ArgsHead),
             notin(vble(X), BodyVbles)),    % vble(X) is not a member of BodyVbles
            OpVbles), !,
    nl, nl,nl,write_term('---------- Error: orphan variable is found in: ----------'), nl,
    write_term(Axiom), nl, write_term(OpVbles).

orphanVb(_, []).

prop(+[PT| ArgsT], [PT| ArgsT]).
prop(-[PT| ArgsT], [PT| ArgsT]).



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
    readFile(Stream, String): read Stream
    Input:  Stream:
    Output: String is the content in file Stream
***********************************************************************************************************************/
readFile(Stream,[]) :-
    at_end_of_stream(Stream), !.

readFile(Stream,[X|L]) :-
    \+ at_end_of_stream(Stream),
    read(Stream,X),
    readFile(Stream,L).

/**********************************************************************************************************************
    readInputs(InpFileList, InpDataList)
            Read input files and return the corresponding input data.
    Input:  InpFileList is a list of the directories of input files
    Output: A list of input data.
************************************************************************************************************************/
readInputs([], []).
readInputs([FileIn| Rest], [InpData| RestInp]):-
  open(FileIn, read, StrInp),
  readFile(StrInp, Inp),       % the input abox is a list
  delete(Inp, end_of_file, InpData),
  close(StrInp),
  readInputs(Rest, RestInp).


% remove " in files
removeQuote(FileList):-
    readInputs(FileList, DataList),
    writeFiles(FileList, DataList).
/**********************************************************************************************
  replace(E, SubE, ListIn,ListOut): replace element E in ListIn with SubE to get ListOut.
  If E does not occur in the list, ListOut = ListIn.
***********************************************************************************************/
replace([], List, List):-!.
replace((_, _), [], []):-!.
replace((E, SubE), ListIn,ListOut):- replace(E, SubE, ListIn,ListOut).
replace([(E, SubE)| Rest], ListIn,ListOut):-
  replace(E, SubE, ListIn,ListTem),
  replace(Rest, ListTem, ListOut).

replace(_, _, [], []):-!.
replace(E, SubE, [H|T], [SubE|T2]) :- H = E, replace(E, SubE, T, T2), !.
replace(E, SubE, [H|T], [H|T2]) :- H \= E, replace(E, SubE, T, T2).


replaceS(E, ListIn, ListOut):-
  replace(E, ListIn,ListOut).

replaceS(E, SubE, ListIn, ListOut):-
  replace(E, SubE, ListIn,ListOut).


/**********************************************************************************************
    replacePos(P, ListIn, Sub, ListOut): only replace position P in ListIn with Sub to get ListOut.
    Counting from 0: replacePos(1, [0,1,2,3], d, X). X = [0, d, 2, 3].
***********************************************************************************************/
% Step case: find Ith argument and recurse on it
replacePos(_, [],_, []):-!.
replacePos(P, ListIn, Sub, ListOut) :-
    split_at(P, ListIn, FronList, [_| AfterList]),
    split_at(P, ListOut, FronList, [Sub| AfterList]).

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


/**********************************************************************************************
    From http://www.swi-prolog.org/
    split_at(N,List1, List2, List3) let the following true:
    append(List2, List3, List1),
    length(List2, N),
    split_at(1, [0,1,2], X, Y). X = [0],    Y = [1, 2].
**********************************************************************************************/
split_at(0,L,[],L) :- !.
split_at(N,[H|T],[H|L1],L2) :-
     M is N -1,
    split_at(M,T,L1,L2).

% split([e,d,r,a,g,r],a,X,Y): X = [e, d, r, a],Y = [g, r].
split([], _, _, _):- fail.
split(List, Ele, SubList1, SubList2):-
    append(SubList1,  SubList2, List),
    last(SubList1, Ele).
/**********************************************************************************************

% subst(V/E,E1,E2): E2 is the result of replacing E with V in E1.
**********************************************************************************************/

subst([Subst|Substs], E,NE) :- subst(Subst,E,NE1), subst(Substs,NE1,NE), !.
subst(_,[],[]) :-!.                          % If E1 is empty problem then do nothing
subst([],E,E) :-!.
subst(C/C, E, E):- arg(C), !.

%subst(Subst,[F|Args1],[F|Args2]) :-
  % atomic(F), maplist(subst(Subst),Args1,Args2),!. % If E1 is compound then recurse on args.
subst(Subst,[E1=E2|Tl],[NE1=NE2|NTl]) :-       % If E1 is unification problem then
   subst(Subst,E1,NE1), subst(Subst,E2,NE2),   % apply substitution to both sides
   subst(Subst,Tl,NTl),!.                        % then recurse on tails

subst(Subst,[+E|T],[+NE|NT]) :-         % for substituting resolution ready clauses
   subst(Subst,E,NE),!,
   subst(Subst,T,NT).

subst(Subst,[-E|T],[-NE|NT]) :-
   subst(Subst,E,NE),!,
   subst(Subst,T,NT).

subst(Subst,[V/E|T], [NV/E|NT]) :-          % If E1 is substitution then
   subst(Subst,V,NV),!,                    % apply substitution to value
   subst(Subst,T,NT).                      % then recurse on tails

subst(Subst, [Els1|T], [Els2|TSub]) :-
  subst(Subst, Els1, Els2),!,
  subst(Subst, T, TSub). % If E1 is compound then recurse on args.



% only substitute a constant, which is a list of one element, or a variable, which is vble(X).
subst(_/C, Y, Y):- %arg(C), arg(Y),
    Y \= C, !.
subst(D/C, C, D):- arg(C), arg(D),  !.

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


/**********************************************************************************************************************
    theoryGraph(Graph): the theory graph based on rules.
    1. the head of the clause will be in the front of it.
    2. the equalities/inequalities literals will be the end of its body.
    3. the equalities will be in front of the inequalities.
    * the order is for the reduce the search space of sl resolution.
************************************************************************************************************************/
theoryGraph(Theory, Graph):-
    findall(Branch,
            (member([+[Pred|_]], Theory),    % get an axiom Q, whose predicate is Pred.
             extBranch(Theory, [Pred], Branch)),
            Branches),
    sort(Branches, Graph).

% get the branch by extending BranchIn.
extBranch(Rules, BranchIn, BranchOut):-
    last(BranchIn, Pred),
    member([+[Pred2|_]|Body], Rules),
    delete(Rules, [+[Pred2|_]|Body], RestTheory),
    occur(-[Pred|_], Body),
    (notin(Pred2, BranchIn)-> append(BranchIn, [Pred2], BranchNew), !;
     member(Pred2, BranchIn)-> BranchNew = BranchIn),
    extBranch(RestTheory, BranchNew, BranchOut).
extBranch(_, Branch, Branch).


/**********************************************************************************************************************
    notUnique(LF, Abox, Rules): true if F's occurances is more than once
        Input:  F: a constant/predicate;
                Abox, Rules: input KG and rules.
************************************************************************************************************************/
notUnique(F, Abox, Rules):-
    occ2s(F, Abox, 0,  NumA),
    occ2s(F, Rules, 0, NumR),
    NumA + NumR > 1.

% check whether F occcurs at least 2 times. The returned counting would be 0, 1 or 2.
occ2s(_, [], Num, Num).
occ2s(F, [Axiom| RestAxioms], NumIn, NumNew):-
    NumIn <2, !,
    findall(Prop, (member(+Prop, Axiom); member(-Prop, Axiom)),
            AllProp),
    flatten(AllProp, Props),
    delete(Props, F, PRest),
    length(Props, L1),
    length(PRest, L2),
    NumTem is L1 - L2 + NumIn,
    occ2s(F, RestAxioms, NumTem, NumNew).
% Num = 2, terminate
occ2s(_, _, Num, Num).


/* pairwise(L1,L2,Pairlist): pairs up corresponding elements of two lists.
e.g.,pairwise([equal,[tories],[conservatives]], [equal,vble(y),vble(z)],X).
X = [equal=equal, [tories]=vble(y), [conservatives]=vble(z)].
*/
% Base case
pairwise([],[],[]).             % If input two empty lists then return one.

pairwise([[H1]|T1],[[H2]|T2], POut) :- % Otherwise, pair up the heads
     pairwise(H1, H2, NewP),
     pairwise(T1,T2,T),
     append(NewP, T, POut).                % and recurse on the tails.

% Step case
pairwise([H1|T1],[H2|T2],[H1=H2|T]) :- % Otherwise, pair up the heads
     pairwise(T1,T2,T).                % and recurse on the tails.

%
/**********************************************************************************************************************
    relAxiom(AboxF, RulesF, PST, PSF, RelAboxF, RelRulesF): extract the relevant triples and rules based on PS
    Input:  AboxF and RulesF are the directories of the original KG.
            PST, PSF  are the directories of the true set and false set of the preferred structure.
            HeuF is the directory of the heuristics file.
    Output: RelAboxF is the file of the relevant triples.
            HeuF is expanded with the theory graph.


relAxiom(AboxF, RulesF, PST, PSF, HeuF, RelAboxF):-
  % get the inputs: the banned and applied repairs; heuristics and the proofs of sufficiencies and insufficiencies
  init([AboxF, RulesF, PST, PSF],  [Abox, Rules, TrueSetE, FalseSetE]),
  theoryGraph(Rules, Graph),
  open(HeuF, write, StreamHeuF),
  write_term(StreamHeuF, 'TheoryGraph: '),
  write_term(StreamHeuF, Graph),
  append(TrueSetE, FalseSetE, PS),

  % Get all triples that contain constants/individuals involved in PS.
  findall([+[P2| Args2]],
          (member([+[P| Args1]], PS),
           member([+[P2| Args2]], Abox),
           intersection(Args1, Args2, [_])),  % contain at least one same constant.
           TriplesRle1),

  append(PS, TriplesRle1, TargetTriples),

  % Get all relevant predicates.
  findall(Pred,
          (member([+[P| _]], TargetTriples),
           member(Branch, Graph),
           member(P, Branch),)
          PredR),

  % find all newly discovered relevant triples based on PredR.
  findall([+[P| Args1]],
          (member([+[P| Args1]], Abox),
           member(P, PredR),
           notin([+[P| Args1]], TriplesRle1)),
           TriplesRle2),
  % get the new Abox which only contain relevant triples.
  append(TriplesRle1, TriplesRle2, AboxNew),
  length(AboxNew, AboxNewLen),
  length(Abox, AboxLen),
  write('There are '), write_term(AboxNewLen),
  write(' relevant triples out of '), write_term(AboxLen),

  % write the relevant Abox to the output file.
  open(RelAboxF, write, StreamRelAbox),
  write_term(StreamRelAbox, AboxNew).

************************************************************************************************************************/

/**********************************************************************************************************************
    writeLog: write log files.
    This function is unavailable in python-swipl ABC.
***********************************************************************************************************************/
writeLogSep(_).
writeLog(_).

/**********************************************************************************************************************
    writeFile(Directory, OutFiles, DataList)
            Write output files in Directory with the given output data.
    Input:  Directory is the directory of output files.
            FileName is a list of the names of output files.
            DataList is a list of output data to write in order.
***********************************************************************************************************************/
writeFiles(_, [], []).
writeFiles(Directory, [FileName| RestNames], [Data| RestData]):-
  atom_concat(Directory, FileName, FilePath),
  open(FilePath, write, StreamFile),
  % write a list line by line
  writeAll(StreamFile, Data),
  close(StreamFile),
  writeFiles(Directory, RestNames, RestData).

% FileName is the full path.
writeFiles([], []).
writeFiles([FileName| RestNames], [Data| RestData]):-
  open(FileName, write, StreamFile),
  % write a list line by line
  writeAll(StreamFile, Data),
  close(StreamFile),
  writeFiles(RestNames, RestData).


% write a list line by line
writeAll(_, []):- !.
writeAll(Stream1,[C|Cs]) :- write(Stream1, C), write(Stream1, '.'), nl(Stream1), writeAll(Stream1, Cs).
