axiom([+a(3)]).
axiom([+b(6)]).
axiom([-a(\x), -b(\y), -func(smaller,\x,\y), +isSmaller(\x,\y)]).


smaller(X,Y) :-
    X < Y.

%Success: axiom(X), length(X,Y), Y is 4, Z = -func(FuncName,_,_), nth1(3,X,Z), call(FuncName,2,5).  % True.
%Success: axiom(X), length(X,Y), Y is 4, Z = -func(FuncName,_,_), nth1(3,X,Z), call(FuncName,5,2).  % False.
