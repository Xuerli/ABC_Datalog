% ['Monkeypox is an infectious disease caused by the monkeypox virus.', 
% 'Monkeypox virus can occur in certain animals, including monkey.', 
% 'Humans are mammals.', 
% 'Mammals are animals.', 
% 'Symptons of Monkeypox include fever, headache, muscle pains, feeling tired, and so on.', 
% 'People feel tired when they get a flu.']	

% ['∃x (OccurMonkeypoxVirus(x) ∧ GetMonkeypox(x))', 
% '∃x (Animal(x) ∧ OccurMonkeypoxVirus(x))', 
% '∀x (Human(x) → Mammal(x))', 
% '∀x (Mammal(x) → Animal(x))', 
% '∃x (GetMonkeypox(x) ∧ (Fever(x) ∨ Headache(x) ∨ MusclePain(x) ∨ Tired(x)))', 
% '∀x (Human(x) ∧ Flu(x) → Tired(x))']	

% There is an animal.	

% ∃x (Animal(x))	

% True

%Note: This example shows importance of renaming skolem constants to get the desired theory representation
:- working_directory(_, '../src').
:-[main].

logic(fol).
theoryName(monkeypox).

axiom([+occurMonkeyPox(c1)]).
axiom([+getMonkeyPox(c1)]).
axiom([+animal(c2)]).
axiom([+occurMonkeyPox(c2)]).
axiom([-human(\x), +mammal(\x)]).
axiom([-mammal(\y), +animal(\y)]).
axiom([+getMonkeyPox(c3)]).
axiom([+tired(c3)]).
axiom([-human(\z), -flu(\z), +tired(\z)]).

trueSet([getMonkeyPox(human),animal(monkey)]).  %2 insuff, 1 incomp
falseSet([animal(c2)]).
protect([]).
heuristics([]).

theoryFile:- pass.

% GS
% axiom([+occurMonkeyPox(c1)]).
% axiom([+getMonkeyPox(c1)]).
% axiom([+animal(monkey)]).
% axiom([+occurMonkeyPox(monkey)]).
% axiom([-human(\x), +mammal(\x)]).
% axiom([-mammal(\y), +animal(\y)]).
% axiom([+getMonkeyPox(human)]).
% axiom([+tired(human)]).
% axiom([-human(\z), -flu(\z), +tired(\z)]).