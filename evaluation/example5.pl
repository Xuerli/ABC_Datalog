% ['A podcast is not a novel.', 
% '[BG] If a person is born in American City, the person is American.', 
% '[BG] If a book is novel and it is written by a person, then the person is a novel writer.', 
% 'Dani Shapiro is an American writer.', 
% 'Family History is written by Dani Shapiro.', 
% 'Family History is a novel written in 2003.', 
% 'Dani Shapiro created a podcast called Family Secrets.', 
% '[BG] Boston is an American city.']	
% ['∀x (IsPodcast(x) → ¬IsNovel(x))', 
% '∀x ∃y (BornIn(x, y) ∧ IsCity(y) ∧ IsAmerican(y) → IsAmerican(x))', 
% '∀x ∀y (IsNovel(x) ∧ WrittenBy(x, y) → WritesNovel(y))',
%  'IsAmerican(dani_Shapiro) ∧ IsWriter(dani_Shapiro)', 
%  'WrittenBy(family_History, dani_Shapiro)', '
%  IsNovel(family_History) ∧ WrittenIn(family_History, y2003)', 
%  'IsPodcast(family_Secrets) ∧ CreatedBy(family_Secrets, dani_Shapiro)', 
%  'IsCity(boston) ∧ IsAmerican(boston)']	
 
%  Dani Shapiro is a novel writer.	WritesNovel(dani_Shapiro)	True
%  Dani Shapiro was born in Boston.	BornIn(dani_Shapiro, boston)	Uncertain
%  Family Secrets is a novel.	IsNovel(family_Secrets)	False



%Examples with functions
:- working_directory(_, '../src').
:-[main].

logic(fol).

theoryName(authors).


axiom([-isPodCast(\x), -isNovel(\x)]).
axiom([-bornIn(\y,f(\y)),-isCity(f(\y)),-isAmerican(f(\y)),+isAmerican(\y)]).
axiom([-isNovel(\a),-writtenBy(\a,\b),+writesNovel(\b)]).
axiom([+isAmerican(dani)]).
axiom([+isWriter(dani)]).
axiom([+writtenBy(familyHistory,dani)]).
axiom([+isNovel(familyHistory)]).
axiom([+writtenIn(familyHistory,y2003)]).
axiom([+isPodCast(familySecrets)]).
axiom([+createdBy(familySecrets,dani)]).
axiom([+isCity(boston)]).
axiom([+isAmerican(boston)]).

eqAxiom([f(dani),boston]).

trueSet([bornIn(dani,boston)]). %1 insuff, 1 incomp
falseSet([writesNovel(dani)]).
protect([]).
heuristics([]).

theoryFile:- pass.
%GS
% axiom([+bornIn(dani,f(dani))]). %further: generalize
% axiom([-isPodCast(\x), -isNovel(\x)]).
% axiom([-bornIn(\y,f(\y)),-isCity(f(\y)),-isAmerican(f(\y)),+isAmerican(\y)]).
% axiom([-isNovel(\a),-writtenBy(\a,\b),+writesNovel(\b)]).
% axiom([+isAmerican(dani)]).
% axiom([+isWriter(dani)]).
% axiom([+writtenBy(familyHistory,dani)]).
% axiom([+writtenIn(familyHistory,y2003)]).
% axiom([+isPodCast(familySecrets)]).
% axiom([+createdBy(familySecrets,dani)]).
% axiom([+isCity(boston)]).
% axiom([+isAmerican(boston)]).
