axiom([-sdf,+sdf]).
isSdf(sdf).

abc:-
    axiom(U),
    (member(+X,U),isSdf(X);member(-X,U),isSdf(X)),
    print(X).
    