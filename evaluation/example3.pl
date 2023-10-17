% ['A Japanese game company created the game the Legend of Zelda.',
%  'All games in the Top 10 list are made by Japanese game companies.', 
%  '[BG] If a game sells more than one million copies, then it will be selected into the Top 10 list.', 
%  'The Legend of Zelda sold more than one million copies.']	

%  ['∃x (Japanese(x) ∧ VideoGameCompany(x) ∧ Game(thelegendofzelda) ∧ Created(x, thelegendofzelda))', 
%  '∀x ∀y (Game(x) ∧ InTop10(x) ∧ Created(x, y) → Japanese(y))', 
%  '∀x (Game(x) ∧ SellsMoreThan(x, onemillioncopies) → Top10(x))', 
%  'SellsMoreThan(thelegendofzelda, onemillioncopies)']	


%  The Legend of Zelda is in the Top 10 list.
%  	Top10(thelegendofzelda)	
%     True
:- working_directory(_, '../code').
:-[main].

theoryName(videogame).


% axiom([+japanese(c1)]).
axiom([+videoGameCompany(c1)]).
axiom([+game(thelegendofzelda)]).
axiom([+created(c1,thelegendofzelda)]).
axiom([-game(\x), -intop10(\x), -created(\y,\x),-videoGameCompany(\y), +japanese(\y)]).
axiom([-game(\z), -sellmorethan(\z,onemillioncopies), +intop10(\z)]).
axiom([+sellmorethan(thelegendofzelda,onemillioncopies)]).

trueSet([intop10(thelegendofzelda),created(nintendo,thelegendofzelda),japanese(nintendo)]). %1 suff, 2 insuff
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.

%GS
% axiom([+videoGameCompany(nintendo)]).
% axiom([+game(thelegendofzelda)]).
% axiom([+created(nintendo,thelegendofzelda)]).
% axiom([-game(\x), -intop10(\x), -created(\y,\x),-videoGameCompany(\y), +japanese(\y)]).
% axiom([-game(\z), -sellmorethan(\z,onemillioncopies), +intop10(\z)]).
% axiom([+sellmorethan(thelegendofzelda,onemillioncopies)]).

% trueSet([intop10(thelegendofzelda),created(nintendo,thelegendofzelda),japanese(nintendo)]). %Should be insufficient.
% falseSet([]).
% protect([]).
% heuristics([]).