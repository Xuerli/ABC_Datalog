/*
Update Date: 06.03.2022
*/
:-[util].

/**********************************************************************************************************************
    vitality(FaultStateIn, TheoryIn, VitState, ScoresTem, TotalScores):
            Sum the entrenchment of all axioms in the input theory.
    Input:  FaultStateIn = (SuffsIn, _, IncompsIn)
            TheoryIn: the true set given by preferred structure which contains all preferred sentences.
            SuffsIn is a list of proofs of sufficiencies [(Goal1, Proofs),...]
            IncompsIn a list of proofs of incompatiblities.  [(Goal1, Proofs), ....]
            VitStateTem: initial should be [], which is used to temporary record middle results.
            ScoresIn: initial should be (0,0).
    Output:
            VitState: the entrenchment of each axioms.
            VitState = [[(e1, e2), Axiom1], ...] where e1 = s1- incom1, e2 = s2 -
            TotalScores = (totalE1, totalE2).
************************************************************************************************************************/

vitality(_, [],  VitState, VitState, TotalScores, TotalScores).
vitality((SuffsIn, _, IncompsIn), [Axiom|RestAs], VitStateTem, VitState, (T1,T2), TotalScores):-
  findall(Goal1,
        (member((Goal1, Proofs), SuffsIn),	% get an sufficiency of which Goal1 is from T(PS) with Proofs.
         forall(member(Proof, Proofs), member((_, Axiom,_,_,_), Proof))),	% the axiom is involved in all proofs.
	EssGolasTure), % the list of goals from the true set of PS of which Axiom contributes all proofs.
    length(EssGolasTure,  E1),
  findall(Goal1,
        (member((Goal1, Proofs), IncompsIn),	% get an incompatibility of which Goal1 is from F(PS) with Proofs.
         forall(member(Proof, Proofs), member((_, Axiom,_,_,_), Proof))),	% the axiom is involved in all proofs.
	EssGolasFalse), % the list of goals from the false set of PS of which Axiom contributes all proofs.
    length(EssGolasFalse,  E2),

  findall(C,
        (member((Goal1, Proofs), SuffsIn),	% get an sufficiency of which Goal1 is from T(PS) with Proofs.
         \+member(Goal1, EssGolasTure),               % do not consider the goal to which Axiom is essential.
         length(Proofs, Num1),
         (Num1 = 0-> C = 0;
          Num1 \= 0,
          findall(Proof,
                 (member(Proof, Proofs),
                  member((_, Axiom,_,_,_), Proof)),
                 Aproofs),	% get all proofs that axioms is involved.
          length(Aproofs, Num2),
          C is Num2/Num1)),
	CList), % the list of goals from the true set of PS of which Axiom contributes all proofs.
    sum_list(CList,  C1),

    findall(C,
	(member((Goal1, Proofs), IncompsIn),	% get an incompatibility of which Goal1 is from F(PS) with Proofs.
         \+member(Goal1, EssGolasFalse),               % do not consider the goal to which Axiom is essential.
         length(Proofs, Num1),
         (Num1 = 0-> C = 0;
          Num1 \= 0,
          findall(Proof,
                 (member(Proof, Proofs),
                  member((_, Axiom,_,_,_), Proof)),
                 Aproofs),	% get all proofs that axioms is involved.
          length(Aproofs, Num2),
          C is Num2/Num1)),
	CList2), % the list of goals from the true set of PS of which Axiom contributes all proofs.
    sum_list(CList2,  C2),
    Ent1 is E1-E2,
    Ent2 is C1-C2,
    VitAxiom = [(Ent1, Ent2), Axiom],
    T1new is Ent1 + T1,
    T2new is Ent2 + T2,
    vitality((SuffsIn, _, IncompsIn), RestAs, [VitAxiom| VitStateTem], VitState, (T1new, T2new), TotalScores).





/**********************************************************************************************************************
    preDistance(Predicate, TrueSet, FalseSet, Theory, Distance):
            Calculate the absolute distance of Predicate to the preferred structure.
    Input:  Predicate: the object predicate, e.g., [mum].
            TrueSet: the true set given by preferred structure which contains all preferred sentences.
            FauseSet: the false set given by preferred structure which contains all violative sentences.
            CurrentDist: the current distance.
    Output:
            Distance: the absolute distance of the Predicate.
************************************************************************************************************************/
preDistance([], _, _, _, infinite):-!.
preDistance(_, [], [], _, infinite):-!.
preDistance(Predicate, TrueSet, FalseSet, Theory, AbsDistance):-
    setof(Predicate, member(([+Predicate| T],_),TrueSet),PPs),
    setof(Predicate, member(([+Predicate|T],_),FalseSet),VPs),
    append(PPs,VPs, PPAll),    % get all predicates in preferred structure.
    paths([[Predicate]], PPAll, Theory, [], Paths),
    findall(Dis, (member(Path, Paths), length(Path, Dis)), DisList),
    sort(DisList, [AbsDistance|_]).



/**********************************************************************************************************************
    paths(PathIn, PPs, Theory, PathsIn, Paths):
            Get paths from the Predicate to a predicate in PPs.
    Input:  Predicate: the object predicate, e.g., [mum].
            PPs: the preferred predicates which occur in the preferred structure.
            Theory: the input theory.
            PathIn: the found paths from the predicate to a preferred predicate.
    Output:
            Paths: the paths from the Predicate to a predicate in PPs.
************************************************************************************************************************/
paths(_, [], _,_,[]):-    !.
paths([],_,_,Paths, Paths):- !.
paths([[P|T]|RestBranches], PPs, Theory, PathsIn, PathsOut):-
    member(P,PPs),!,    % Reach a predicate P, which occurs in the preferred structure.
    paths([RestBranches], PPs, Theory, [[P|T]|PathsIn], PathsOut).

% Expand the first branch with all its children.
paths([[P|T]|RestBranches], PPs, Theory, PathsIn, PathsOut):-
    setof(Branch,
        (member((Clause,_), Theory),
         member(-[P|_],Clause),
          member(+[HeadP|_],Clause),       % Get head predicate in rule Clause
         Branch=[HeadP|[P|T]]),
        Branches),!,
    append(Branches, RestBranches, NewBranches),
    paths(NewBranches, PPs, Theory, PathsIn, PathsOut).

% Drop the first branch if it is an dead end.
paths([_|RestBranches], PPs, Theory, PathsIn, PathsOut):- !,
    paths(RestBranches, PPs, Theory, PathsIn, PathsOut).
