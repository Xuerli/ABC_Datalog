:- working_directory(_, '../code').
:-[main].

theoryName(animals).


axiom([+occurMonkeyPox(c1)]).
axiom([+getMonkeyPox(c1)]).
axiom([+animal(c2)]).
axiom([+occurMonkeyPox(c2)]).
axiom([-human(\x), +mammal(\x)]).
axiom([-mammal(\y), +animal(\y)]).
axiom([+getMonkeyPox(c3)]).
axiom([+tired(c3)]).
axiom([-human(\z), -flu(\z), +tired(\z)]).

trueSet([getMonkeyPox(human),animal(monkey)]). 
falseSet([animal(c2)]).
protect([]).
heuristics([]).

theoryFile:- pass.