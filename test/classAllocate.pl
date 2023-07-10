:- working_directory(_, '../code').
:-[main].

theoryName(classAllocate).


axiom([+oldClassSize(elite,15)]).
axiom([+oldClassSize(normal,14)]).
axiom([+score(t1,paul,69)]).
axiom([+score(t2,paul,71)]).
axiom([-score(t1,\x,\y),-score(t2,\x,\z),-acceptScoreElite(avg(\y,\z)),+allocate(\x,elite)]).
axiom([-score(t1,\a,\b),-score(t2,\a,\c),-acceptScoreNormal(avg(\b,\c)),+allocate(\a,normal)]).
axiom([+acceptScoreElite(70)]).
axiom([+acceptScoreNormal(69)]).
axiom([-acceptScoreElite(\d),-acceptScoreNormal(\d)]).
axiom([-oldClassSize(\e,\f),-allocate(\g,\e),+newClassSize(\e,suc(\f))]).

eqAxiom([avg(69,71),70]).
eqAxiom([suc(14),15]).
eqAxiom([suc(15),16]).


% avg(X,Y,Z):-
%     Z is integer((X+Y)/2).

% trueSet([]).
trueSet([allocate(paul,normal)]). %,
falseSet([newClassSize(normal,16),newClassSize(elite,16)]).
protect([]).
heuristics([]).

theoryFile:- pass.
