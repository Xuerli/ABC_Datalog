axiom([q,r,y,i,op,p]).
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

loopAll(L):-
    is_list(L),
    findall(Ls, compute(L,[],[],Ls),Ans), % can use setof if there will be duplicates but do not want
    print(Ans),nl,
    length(Ans,X),
    print(X),nl.

startdo:-
    axiom(X),
    loopAll(X),
    !.
