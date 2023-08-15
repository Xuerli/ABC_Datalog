% ['There are six types of wild turkeys: Eastern wild turkey, Osceola wild turkey, Gould’s wild turkey, Merriam’s wild', 
% 'turkey, Rio Grande wild turkey, and Ocellated wild turkey.', 
% 'Tom is not an Eastern wild turkey.', 
% 'Tom is not an Osceola wild turkey.', 
% "Tom is also not a Gould's wild turkey, or a Merriam's wild turkey, or a Rio Grande wild turkey.", 
% 'Tom is a wild turkey.']	
% ['∀x (WildTurkey(x) → (Eastern(x) ∨ Osceola(x) ∨ Goulds(x) ∨ Merriams(x) ∨ Riogrande(x) ∨ Ocellated(x)))', 
% '¬(WildTurkey(tom) ∧ Eastern(tom))', 
% '¬(WildTurkey(tom) ∧ Osceola(tom))', 
% 'WildTurkey(tom) → ¬(Goulds(tom) ∨ Merriams(tom) ∨ Riogrande(tom))', 
% 'WildTurkey(tom)']	

% Tom is an Eastern wild turkey.	Eastern(tom)	False
% Tom is an Ocellated wild turkey.	Ocellated(tom)	True

:- working_directory(_, '../code').
:-[main].

theoryName(turkey).


axiom([-wildTurkey(\x),+eastern(\x),+osceola(\x),+goulds(\x),+merriams(\x),+riogrande(\x),+ocellated(\x)]).
axiom([-wildTurkey(tom), -eastern(tom)]).
axiom([-wildTurkey(tom), -osceola(tom)]).
axiom([-wildTurkey(tom), -goulds(tom)]).
axiom([-wildTurkey(tom), -merriams(tom)]).
axiom([-wildTurkey(tom), -riogrande(tom)]).
axiom([+wildTurkey(tom)]).

trueSet([eastern(tom)]). 
falseSet([goulds(tom),ocellated(tom)]).
protect([]).
heuristics([noOpt]).

theoryFile:- pass.