axiom([[a,b,c],[a,b],[b,c]]).
doSomething(A):-
    print(A),nl.

compute([],[],L,L).

compute([H|R],Rem,L,A):- %Choose to append H to L
    doSomething(H), %Processing of H
    append(L,[H],L2),
    append(R,Rem,R2),
    compute(R2,[],L2,A).

compute([H|R],Rem,L,A):- %Choose not to append H to L (only if length of R > 0)
    length(R,LR), LR > 0,
    append(Rem,[H],Rem2),
    compute(R,Rem2,L,A).

% search([H|R],X,H):-
%     member(X,H).
% search([H|R],X,Out):-
%     search(R,X,Out).


loopAll(L):-
    is_list(L),
    findall(Ls, search(L,a,Ls),Ans), % can use setof if there will be duplicates but do not want
    print(Ans),nl,
    length(Ans,X),
    print(X),nl.

startdo:-
    axiom(X),
    loopAll(X),
    !.


memberNested(Elem,List):-
    member(Elem,List),!.

memberNested(Elem,[H|_]):-
    is_list(H),
    memberNested(Elem,H).

memberNested(Elem,[_|R]):-
    memberNested(Elem,R).

memberNested(_,[]):- fail.