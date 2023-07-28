axiom([-sdf,+sdf]).
isSdf(sdf).

isOpSign(+_,-_).
isOpSign(-_,+_).

abc:-
    axiom(U),
    (member(+X,U),isSdf(X);member(-X,U),isSdf(X)),
    print(X).
    