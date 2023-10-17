
abc :-
    \+current_predicate(logic/1),!,
    write('No logic specified.'),nl.

abc :-
    logic(fol),!,
    write('Running FOL version...'),nl,
    working_directory(_,'./ABC_FOL'),
    [abc],
    main.

abc :-
    logic(datalog),!,
    write('Running Datalog Version...'),nl,
    working_directory(_,'./ABC_Datalog'),
    [abc],
    main.

abc :-
    write('Unsupported logic.'),nl.