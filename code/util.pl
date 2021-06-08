/*
Date: 07 Jan 2019




*/

:- dynamic verbose/1,  verbose(off).
% Keeps track of the current result of unification (FS) which is known at the end of recursion in reform2.
:- dynamic unifResult/0.



refSuccess :- unifResult,!.
unifResult(fail) :- \+(unifResult),!.


%  working_directory(_,"/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/"). [main,theories/door].
negateCl([],[]).
negateCl([H|L], [H1| L1]):- negate(H, H1), negateCl(L, L1).

%% negate a literal.
negate(+X,-X):- !.
negate(-X,+X):-!.
negate([+X],[-X]):-!.
negate([-X],[+X]):-!.
negate([X],[-X]):-!.
negate(X,-X).
negate([],[]).
pos(X,+X).

sign(+[_], pos).
sign(-[_], neg).


%% nthProp(Ith, Clause, Prop): Proposition of the nth literal in Clause is Prop.
nthProp(Ith, Clause, Prop):- nth1(Ith, Clause, +Prop), !.
nthProp(Ith, Clause, Prop):- nth1(Ith, Clause, -Prop), !.


/**********************************************************************************************************************
    convertClause(In, Clause): convert input axiom into Horn clause form with head at the front and body in the end.
    Input:    In is an input axiom
    Output: Clause is a Horn clause.
        For reducing the search space of resolution, the Clause has its head at the front and body in the end.
************************************************************************************************************************/
convertClause(AxiomIn, Clause) :-
    appEach(AxiomIn, [appLiteral, convert],  Clause1),
    sort(Clause1, Clause).        % Remove duplicate literals and sort literals where positive literal will be the head of Clause.


%% convert(In,Out): convert normal Prolog syntax to internal representation or
%% vice versa.

%% These variable/constant conventions need revisiting for serious use

% X is a variable
convert(\X,vble(X)) :-  !.                      % Convert X into a variable
/*    atom_chars(X,[?|T]),              % variable is start with ?
    Out = vble(T),!.
    atomic(X), atom_chars(X,[H|_]),             % if first letter
    char_code(H,N), 109<N, N<123, !.            % is n-z
*/

convert(vble(X),vble(X)) :-  !.                      % Convert X into a variable

% A is a constant
convert(A,[A]) :-             % Convert A into a constant, where A is either an atom or a number
    atomic(A), !.

% A is a number
convert(A,[A]) :-             % Convert A into a constant
    number(A),!.



% E is compound
convert(E,[F|NArgs]) :-
    var(E), !,                                  % If E is output and input compound
    maplist(convert,Args,NArgs), E=..[F|Args].  % Recurse on all args of F


convert(E,[F|NArgs]) :-                     % If E is input and compound then
    \+ var(E), \+ atomic(E), !,
    E=..[F|Args],  % break it into components
    maplist(convert,Args,NArgs).                % and recurse on them

/*renvert internal representation to normal Prolog syntax */

revert([],[]):- !.

% X is a variable
revert(vble(X),\X) :-  !.                     % revert a variable

% A is a constant or number
revert([A],A) :- !.                          % revert a constant and number

%% These variable/constant conventions need revisiting for serious use
% E is compound
revert(E,E) :-
    atomic(E), !.                               % If E is output and input compound

% E is compound: F(NArgs).
revert(E,FactE) :-
    is_list(E),!,                                  % If E is output and input compound
    E =[F|Args],
    maplist(revert,Args,NArgs), FactE=..[F|NArgs].  % Recurse on all args of F

revert(E,[F|NArgs]) :-
    var(E), !,                                  % If E is output and input compound
    maplist(revert,Args,NArgs), E=..[F|Args].  % Recurse on all args of F


/*
convertForm : convert the form of Cs into the original form of ontology
Input [C1=C2]:[[F,Args]=[F2,Args2]] [loves,vble(x),vble(x)]
Output Ontology: [F(Args),F2(Args2)]
*/
convertForm([], []):- !.
convertForm([C1 = C2], Ontology):- !,
    maplist(revert, C1,Clause1),
    maplist(revert, C2,Clause2),  % list form: [Functor | Args]
    Fact1=..Clause1,                            % axiom form: Functor(Args)
    Fact2=..Clause2,
    Ontology = [[Fact1],[Fact2]].

% Argument1: [ [+[cap_of,[berlin],[germany]]], [+[cap_of,[canberra],[australia]]] ]
% Argument2: [ [+cap_of(berlin,germany)], [+cap_of(canberra,australia)] ]
convertForm([Clause1 | T], Ontology):- !,
  length(Clause1, LengthC),   % Number of the propositions in Clause H.
  adverseEnum(LengthC, LS1),
  findall( Axiom,
          ( member(I1, LS1),
            nth1(I1, Clause1, Literal),        % Literal is the I1th proposition in Clause1.
           (Literal = +Proposition,
              maplist(revert, Proposition, Pnew),
              LNewT =..Pnew,
              Axiom = +LNewT ;
            Literal = -Proposition,
              maplist(revert, Proposition, Pnew),
              LNewT =..Pnew,
              Axiom = -LNewT ;
            Literal \= +_, Literal \= -_,
              maplist(revert, Literal, Pnew),
              Axiom =..Pnew
            )
          ),
          ClauseNew),
          append([ClauseNew], ClauseTrest, Ontology),
        %  Ontology = [ClauseNew| Trest],
          convertForm(T, ClauseTrest).



% produces a list of integers from M up to N in reversed order.
enum(M, M, [M]) :- !.
enum(M, N,List) :-
    N1 is N-1,
    enum(M, N1,Rest),
    List = [N|Rest].

adverseEnum(0,[]) :- !.
adverseEnum(N,List) :-
    Num is N-1,
    adverseEnum(Num, ListFront),
    append(ListFront,[N],List).



% a list of all elements of a List after a term
afterList(C,[C|AfterOnt],AfterOnt) :-!.
afterList(C,[_|Ont],AfterOnt) :-
    afterList(C,Ont,AfterOnt).


%% Not use any more. Get the base of a dummy term.
%% getBaseCons([dummyc1], X).     X = [c].
getBaseCons(Dummyterm, [BaseCons]):-
      Dummyterm = [DummyString],
      string_chars(DummyString, ListCons),
      append([d, u, m, m, y, _], C1, ListCons),
      append(ListOriCons, [_], C1),
      atom_chars(BaseCons, ListOriCons).

oppositeSigns(+L,-R,L,R) :- !.
oppositeSigns(-L,+R,L,R).


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

/**********************************************************************************************
    pairSubs(Cons, Vbles, Subs):
    Input:     Cons: a list of constants.
            Vbles: a list of
    Output: Subs: a list of substitutions by pairing up each pair of constant and variable.
    Example: pairSubs([[c1], [c2]], [vble(x),vble(y)],X).    X = [[c1]/vble(x), [c2]/vble(y)].
**********************************************************************************************/
pairSubs([], [], []):-!.
pairSubs([CH| CT], [VH| VT], [CH/VH| SubT]):-
    pairSubs(CT, VT, SubT).
/**********************************************************************************************
    gensymVble(N, ListOut):
    Input: N is the length of the independent variables list.
    Output: ListOut is the list of independent variables generated by gensym/2.
    * An independent variable starts with iv.
    Example: gensymVble(3,X).  X = [vble(iv6), vble(iv7)|vble(iv8)].
**********************************************************************************************/
gensymVble(1, vble(Exp)):- gensym(iv, Exp), !.
gensymVble(N, [vble(H)|T]):- gensym(iv, H), M is N-1, gensymVble(M, T).

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
    
prop(+[PT| ArgsT], [PT| ArgsT]).
prop(-[PT| ArgsT], [PT| ArgsT]).
/**********************************************************************************************
    mergeAll(ListsInput, [], ListOut) let the following true:
    ListOut = the list of all the elements in the sublists of ListsInput.
**********************************************************************************************/
mergeAll([], ListOut, ListOut):-!.
mergeAll([HList|TList], ListIn, ListOut):-
    merge(HList, ListIn, ListTem1),    % append H and ListIn.
    sort(ListTem1, ListTem2),      % remove duplicates.
    mergeAll(TList, ListTem2, ListOut).
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
        
% drop the last element from the input list
dropTail(ListIn, ListOut):-
    length(ListIn, L), M is L-1,
    split_at(M, ListIn, ListOut, _).
/**********************************************************************************************
    deleteAll(ListsInput, ListDel, ListOut) let the following true:
    ListOut = ListsInput - ListDel
**********************************************************************************************/
deleteAll([], _, []):-!.
deleteAll(ListsInput, [], ListsInput):-!.
deleteAll(ListsInput, [H|T], ListOut):-
    delete(ListsInput, H, ListRest), 
    deleteAll(ListRest, T, ListOut).    

/**********************************************************************************************

    count(E,ListIn,N): The number of term E occur in ListIn is N.
    count(a, [[a,b], [c,d],[a]], 2), or count(a, [[[a],b], [c,d],[[a],d, e]], 2).

**********************************************************************************************/
countTheory(_, [], 0):-!.
countTheory(E, [Clause1| T], N):- countCl(E, Clause1, N1), countTheory(E, T, M), N is M +N1.

countCl(_, [], 0):- !.
countCl(E, [-H| T], N):- !, count(E,H,N1), countCl(E, T, M), N is M + N1.
countCl(E, [+H| T], N):- count(E,H,N1), countCl(E, T, M), N is M + N1.

count(_,[],0):- !.
count(E, [E|T],N) :- count(E,T,N1), N is N1 + 1.
count(E, [[E]|T],N) :- count(E,T,N1), N is N1 + 1.
count(E, [X|T],N) :- X \= E, X\=[E], count(E, T,N).

/*
Part of SWI-Prolog
Author:        Jan Wielemaker
E-mail:        J.Wielemaker@vu.nl
WWW:           http://www.swi-prolog.org
Copyright (c)  2010-2011, University of Amsterdam
All rights reserved.
http://www.swi-prolog.org/pldoc/doc/_SWI_/library/dialect/sicstus/lists.pl?show=src#substitute/4

*/
substitute((Old, List), New, NewList):- substitute_(List, Old, New, NewList),!.
substitute(Old, List, New, NewList) :- substitute_(List, Old, New, NewList).
substitute_([], _, _, []).
substitute_([O|T0], Old, New, [V|T]) :-
    (   Old == O
    ->  V = New
    ;   V = O
    ),
    substitute_(T0, Old, New, T).


/**********************************************************************************************
    unpair(List1, List2, PairsIn, PairsOut): find unpaired members between List1 and List2.
    Input: List1 and List2 are lists to compare.
           PairsIn is the known unpairs between List1 and List2.
    Output: PairsOut is the whole list of inequalities. 
            e.g., unpair([1,2,4], [1,3,5], [], PairsOut). PairsOut = [(2,3), (4,5)].
***********************************************************************************************/
unpair([], [], Pairs, Pairs):-!.
unpair(L1, L2, _, _):- (L1 == [] ; L2 == []), !,fail.
unpair([H1| T1], [H2| T2], PairsIn, PairsOut):-
    H1 == H2 -> unpair(T1, T2, PairsIn, PairsOut);
                unpair(T1, T2, [(H1, H2)|PairsIn], PairsOut).

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
    replace(E, ListIn,ListTem),
    sort(ListTem, ListOut).
        
replaceS(E, SubE, ListIn, ListOut):-
    replace(E, SubE, ListIn,ListTem),
    sort(ListTem, ListOut).


% replace element in the first list with the element on the same position in the second list
replaceLL([E| ET], [SubE| SubET], ListIn, ListOut):-
    replace(E, SubE, ListIn, ListTem),
    replaceLL(ET, SubET, ListTem, ListTem2),
    sort(ListTem2, ListOut).

/**********************************************************************************************
    replacePos(P, ListIn, Sub, ListOut): only replace position P in ListIn with Sub to get ListOut.
    Counting from 0: replacePos(1, [0,1,2,3], d, X). X = [0, d, 2, 3].
***********************************************************************************************/
% Step case: find Ith argument and recurse on it
replacePos(_, [],_, []):-!.
replacePos(P, ListIn, Sub, ListOut) :-
    split_at(P, ListIn, FronList, [_| AfterList]),
    split_at(P, ListOut, FronList, [Sub| AfterList]).

replacePosList([], List,_, List).
replacePosList([H| Rest], ListIn, Sub, ListOut) :-
    replacePos(H, ListIn, Sub, ListTem),
    replacePosList(Rest, ListTem, Sub, ListOut).
/**********************************************************************************************
    repList(ListToRep, Rep, ListIn,ListOut): for each element in ListToRep,
    replace it with Rep in ListIn and get ListOut.
***********************************************************************************************/
repList(_, _, [], []):-!.
repList([], _, List, List):-!.
repList([HEle| TEle], Rep, -ListIn, -ListOut) :- !,
    replace(HEle, Rep, ListIn, ListTem),
    repList(TEle, Rep, -ListTem, -ListOut).
repList([HEle| TEle], Rep, +ListIn, +ListOut) :- !,
    replace(HEle, Rep, ListIn, ListTem),
    repList(TEle, Rep, +ListTem, +ListOut).
repList([HEle| TEle], dummy, ListIn, ListOut) :- !,
    gensym(dummy, NewEle),
    replace(HEle, NewEle, ListIn, ListTem),
    repList(TEle, ListTem, ListOut).
repList([HEle| TEle], Rep, ListIn, ListOut) :- !,
    replace(HEle, Rep, ListIn, ListTem), 
    repList(TEle, Rep, ListTem, ListOut).

/**********************************************************************************************
    combination(List, ArgumentList, Output): the output is a list which combines the elements from each sublists from the input list.
        * e.g., appEach(append, [[1],[2],[3]], [[5]], X), X = [[1, 5], [2, 5], [3, 5]]. 
        * e.g., appEach(sum, [1,2,3], [5], Y). Y = [6, 7, 8]
***********************************************************************************************/
combination([], Out, Out):- !.
combination([H|T], Rec, Out):- 
    member(X, H), 
    (member(X, Rec)->
        RecNew = Rec;
        RecNew = [X|Rec]),
    combination(T, RecNew, Out).
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

/*
appEach([], _, []):- !.    
appEach([H| T], Predicate, [HOut| TOut]):- 
    atom(Predicate),!,
    append([Predicate, H], [HOut],EList),
    Expression =..EList,
    call(Expression),
    appEach(T, Predicate, TOut).
*/    
appEach([], _, []):- !.    
appEach([H| T], [Predicate| Args], Output):- !,
    append([Predicate, H], Args, E1),
    append(E1, [HOut], EList),
    Expression =..EList,
    (call(Expression)-> Output = [HOut| TOut], !;
    \+call(Expression)-> Output = TOut, 
    writeLog([nl,write_term('--Failed to apply '),nl,write_term(Expression),nl,  finishLog])),
    appEach(T, [Predicate| Args], TOut).
    
% Add other arguments in the end.
appEachNth([], _, _, []):- !.    
appEachNth([H| T], N, [Predicate| Args], Output):- !,
    append(Front, Last, [Predicate| Args]),
    length(Front, N),
    append(Front, [H| Last], E1),
    append(E1, [HOut], EList), 
    Expression =..EList,
    (call(Expression)-> Output = [HOut| TOut], !;
    \+call(Expression)-> Output = TOut, 
    writeLog([nl,write_term('--Failed to apply '),nl,write_term(Expression),nl,  finishLog])),
    appEachNth(T, N, [Predicate| Args], TOut).
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
/**********************************************************************************************
    Predicates for write_terming
***********************************************************************************************/
vnl :- verbose(on),nl, !.
vnl.
vwrite_term(X) :- verbose(on), write_term(X), !.
vwrite_term(_).
vwrite_termAll(X) :- verbose(on),write_termAll(X), !.
vwrite_termAll(_).

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

% In datalog, an argument is either a constant, e.g., [c] or a variable, e.g., vble(v).
is_cons(X):- X = [Y], atomic(Y).
arg(X):- is_cons(X); X = vble(_).

% subst(V/E,E1,E2): E2 is the result of replacing E with V in E1.
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

/*
    substRevert(OrigList, GroundList, Subs):- get the substitutions which instantiate OrigList as GroundList.
    Input:     OrigList: the original argument list or proposition
            GroundList: the instantiated proposition/arguments.
    Output: Subs: a list of substitutions.
                    substRevert([a, vble(x),d, vble(d) ],[a, [c], d, [d]], X). 
                    X = [[d]/vble(d), [c]/vble(x)].
*/
substRevert(OrigList, GroundList, Subs):-
    substRevert(OrigList, GroundList, [], Subs).
    
substRevert([], [], Subs, Subs).
substRevert([vble(X)| RestO], [H| RestG], SubsIn, SubsOut):-
    notin(H/vble(X), SubsIn), !, 
    substRevert(RestO, RestG, [H/vble(X)|SubsIn], SubsOut);
    occur(Z/vble(X), SubsIn), Z \= H -> fail, !.
substRevert([H| RestO], [H| RestG], SubsIn, SubsOut):- !,
    substRevert(RestO, RestG, SubsIn, SubsOut).
    
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

occur(_, List):- \+is_list(List), nl,print('ERROR: '), print(List), print(' is not a list'),nl, fail,!.        
occur(X, List):- member(X, List), !.    % avoid redo member(_, List) where '_' is assigned values
notin(_, List):- \+is_list(List), nl,print('ERROR: '), print(List), print(' it is not a list'),nl, fail,!.    
notin(X, List):- \+member(X, List), !.    
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

pruneRedundancy([], Out, Out):- !.
pruneRedundancy([H| T], RecTem, Out):-
    findall(Y, (member(Y, RecTem), forall(member(X, H), member(X, Y))),Ys),
    deleteAll(RecTem, Ys, RecRem),
    pruneRedundancy(T, [H|RecRem], Out).

write_term(X):- write_term(X, [quoted(false)]).

% write_terms  alist line by line
write_termAll([]) :- !.
write_termAll([C|Cs]) :-
    write_term(C, [quoted(false)]),nl, write_termAll(Cs).


% write_term when in a debugging mode.
pprint(X):- debugMode(1)-> call(X); true.

writeLog(_):- spec(debugMode(X)), X \=1, !.
writeLog([]):-!.
writeLog(List):- !, spec(logStream(Stream))-> writeLog(Stream, List).
writeLog(_,[]):-!.
writeLog(_, [finishLog]):-!.
writeLog(Stream, [nl|T]):- nl(Stream), !, writeLog(Stream, T).
writeLog(Stream, [write_term(String)|T]):- 
    write(Stream, String), !,
    writeLog(Stream, T).
writeLog(Stream, [write_termAll(List)|T]):- 
    forall(member(X, List), (write(Stream, X), nl(Stream))),
    writeLog(Stream, T), !.

% write a list line by line
writeAll(_, []):- !.
writeAll(Stream1,[C|Cs]) :- write(Stream1, C), nl(Stream1), writeAll(Stream1, Cs).

