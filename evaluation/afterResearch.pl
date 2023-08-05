:- working_directory(_, '../code').
:-[main].

theoryName(afterResearch).

axiom([-activeReasercher(\x),+writes(\x, papers)]).
axiom([-writes(\x, \y),+author(\x)]).
axiom([-paid(\x),-author(\x),+employee(\x)]).
axiom([+activeReasercher(ann)]).
axiom([+blogger(frankie)]).
axiom([+writes(frankie, blogs)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([activeReasercher(ann), activeReasercher(frankie), paid(frankie), employee(frankie)]).
falseSet([employee(ann), author(frankie)]).
protect([]).
heuristics([]).     %noAxiomAdd

theoryFile:- pass. 
