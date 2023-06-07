:- working_directory(_, '../code').
:-[main].



axiom([+hasCar(car1)]).
axiom([+hasLoad(car1,load1)]).
axiom([+boxShape(load1)]).
axiom([+hasCar(car2)]).
axiom([+hasLoad(car2,load2)]).
axiom([+notboxShape(load2)]).
axiom([-notboxShape(\x), -boxShape(\x)]).
axiom([+hasCar(car3)]).
axiom([+hasCar(car4)]).
axiom([+hasLoad(car4,load3)]).
axiom([+boxShape(load3)]).

trueSet([eastBound(car1),eastBound(car4)]).
falseSet([eastBound(load1),eastBound(car2),eastBound(car3)]).

protect([]).
heuristics([ noAssAdd, noAxiomDele,noRename]).

theoryFile:- pass.
