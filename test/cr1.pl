:- working_directory(_, '../code').
:-[main].

theoryName(cr1).


axiom([-mum(\x,\y),-mum(\z,\y),+eq(\x,\z)]).
axiom([+mum(qu(lily),qu(tina))]).
axiom([+mum(qu(lily),qu(victor))]).
axiom([+mum(qu(anna),qu(victor))]).

trueSet([]).
falseSet([eq(qu(lily),qu(anna))]).
protect([eq]).
heuristics([]).

theoryFile:- pass.
% :- working_directory(_, '../code').
% :-[main].

% theoryName(cr1).


% axiom([-mum(\x,\y),-mum(\z,\y),+eq(\x,\z)]).
% axiom([+mum(lily,tina)]).
% axiom([+mum(lily,victor)]).
% axiom([+mum(anna,victor)]).

% trueSet([]).
% falseSet([eq(anna,lily),eq(lily,anna)]).
% protect([]).
% heuristics([]).

% theoryFile:- pass.
