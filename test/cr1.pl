:- working_directory(_, '../code').
:-[main].

theoryName(cr1).


axiom([-mum(f(\x),\y),-mum(f(\z),\y),+eq(\x,\z)]).
axiom([+mum(f(lily),tina)]).
axiom([+mum(f(lily),victor)]).
axiom([+mum(f(anna),victor)]).

trueSet([]).
falseSet([eq(lily,anna)]).
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
