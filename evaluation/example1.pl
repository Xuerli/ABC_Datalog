% ['If people perform in school talent shows often, then they attend and are very engaged with school events.',
%  'People either perform in school talent shows often or are inactive and disinterested members of their community.', 
%  'If people chaperone high school dances, then they are not students who attend the school.', 
%  'All people who are inactive and disinterested members of their community chaperone high school dances.',
%   'All young children and teenagers who wish to further their academic careers and educational opportunities are students who attend the school.', 
%   'Bonnie either both attends and is very engaged with school events and is a student who attends the school, or she neither attends and is very engaged with school events nor is a student who attends the school. ']
% ['If people perform in school talent shows often, then they attend and are very engaged with school events.', 'People either perform in school talent shows often or are inactive and disinterested members of their community.', 'If people chaperone high school dances, then they are not students who attend the school.', 'All people who are inactive and disinterested members of their community chaperone high school dances.', 'All young children and teenagers who wish to further their academic careers and educational opportunities are students who attend the school.', 'Bonnie either both attends and is very engaged with school events and is a student who attends the school, or she neither attends and is very engaged with school events nor is a student who attends the school. ']	['∀x (TalentShows(x) → Engaged(x))', '∀x (TalentShows(x) ∨ Inactive(x))', '∀x (Chaperone(x) → ¬Students(x))', '∀x (Inactive(x) → Chaperone(x))', '∀x (AcademicCareer(x) → Students(x))', '(Engaged(bonnie) ∧ Students(bonnie)) ⊕ (¬Engaged(bonnie) ∧ ¬Students(bonnie))']	If Bonnie is either both a young child or teenager who wishes to further her academic career and educational opportunities and chaperones high school dances or neither is a young child nor teenager who wishes to further her academic career and educational opportunities, then Bonnie is either a student who attends the school or is an inactive and disinterested member of the community.	AcademicCareer(bonnie) ⊕ Chaperone(bonnie) → AcademicCareer(bonnie) ⊕ Inactive(bonnie)	True
% ['If people perform in school talent shows often, then they attend and are very engaged with school events.', 'People either perform in school talent shows often or are inactive and disinterested members of their community.', 'If people chaperone high school dances, then they are not students who attend the school.', 'All people who are inactive and disinterested members of their community chaperone high school dances.', 'All young children and teenagers who wish to further their academic careers and educational opportunities are students who attend the school.', 'Bonnie either both attends and is very engaged with school events and is a student who attends the school, or she neither attends and is very engaged with school events nor is a student who attends the school. ']	['∀x (TalentShows(x) → Engaged(x))', '∀x (TalentShows(x) ∨ Inactive(x))', '∀x (Chaperone(x) → ¬Students(x))', '∀x (Inactive(x) → Chaperone(x))', '∀x (AcademicCareer(x) → Students(x))', '(Engaged(bonnie) ∧ Students(bonnie)) ⊕ (¬Engaged(bonnie) ∧ ¬Students(bonnie))']	If Bonnie either chaperones high school dances or, if she does not, she performs in school talent shows often, then Bonnie is both a young child or teenager who wishes to further her academic career and educational opportunities and an inactive and disinterested member of the community.	Chaperone(bonnie) ⊕ TalentShows(bonnie) → AcademicCareer(bonnie) ∧ Inactive(bonnie))	False
% ['∀x (TalentShows(x) → Engaged(x))', 
% '∀x (TalentShows(x) ∨ Inactive(x))', 
% '∀x (Chaperone(x) → ¬Students(x))', '
% ∀x (Inactive(x) → Chaperone(x))', 
% '∀x (AcademicCareer(x) → Students(x))', 
% '(Engaged(bonnie) ∧ Students(bonnie)) ⊕ (¬Engaged(bonnie) ∧ ¬Students(bonnie))']	


% Bonnie performs in school talent shows often.	

% Engaged(bonnie)	

% Uncertain

%Shows complex FOL including non-Horn cluases, equivalenc erules (blocked in Datalog due to looping)

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

trueSet([engaged(bonnie)]). 
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Golden Standard
% axiom([+academicCareer(bonnie)]).
% axiom([-talentShows(\x),+engaged(\x)]).
% axiom([+talentShows(\y),+inactive(\y)]).
% axiom([-chaperone(\z),-students(\z)]).
% axiom([-inactive(\a), +chaperone(\a)]).
% axiom([-academicCareer(\b), +students(\b)]).
% axiom([-engaged(bonnie),+students(bonnie)]).
% axiom([-students(bonnie),+engaged(bonnie)]).