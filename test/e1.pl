:- working_directory(_, '../code').
:-[main].

theoryName(talentshow).


axiom([-talentShows(\x),+engaged(\x)]).
axiom([+talentShows(\y),+inactive(\y)]).
axiom([-chaperone(\z),-students(\z)]).
axiom([-inactive(\a), +chaperone(\a)]).
axiom([-academicCareer(\b), +students(\b)]).
axiom([-engaged(bonnie),+students(bonnie)]).
axiom([-students(bonnie),+engaged(bonnie)]).

trueSet([engaged(bonnie)]). %Should be insufficient.
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.