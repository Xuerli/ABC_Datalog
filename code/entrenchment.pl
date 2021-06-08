/*
Date: 07 July 2019




*/

:-[util].


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
    paths([[Predicate]], PPAll, Theory, [],Paths).
    
         

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
        
        
        
        
        
        
        
        
        
        
        