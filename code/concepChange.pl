

:-import(lists).


%:-[entrenchment].

concepChange([], RestSents, RestSents, [], Signature, Signature):-!.

concepChange([(Predicate, Arities)|T], AllSents, RSents, [HRepairs|TRepairs], Signature, NewSig):-      % Uniform the arity of Predicate to the lowest ArityMini.                
    Arities = [(ArityMini, Source)| _],
    HRepairs = arityChange(Predicate, ArityMini),
    findall((Sentence,SS), 
        (((member((Sentence,SS), AllSents), member(+[Predicate|Args], Sentence));
          (member((Sentence,SS), AllSents), member(-[Predicate|Args], Sentence))),
          length(Args, L), 
          L>ArityMini),
          ToReSents),     % Get all sentences which has the predicate but with bigger arity.
    subtract(AllSents, ToReSents, RestSents),
    arityReduce(Predicate, ArityMini, ToReSents, HRSents), % Delete the extra arguments in ToReSents, we get HRSents.
    substitute((Predicate, Arities), Signature, (Predicate, [(ArityMini,Source)]), NewSigTem),  % update signature.
    concepChange(T, RestSents, TRSents, TRepairs, NewSigTem, NewSig),
    append(HRSents, TRSents, RSents).

concepChange([(Predicate, Arities)|T], AllSents, RSents, [HRepairs|TRepairs], Signature, NewSig):-     % Uniform the arity of Predicate to the highest ArityMaxi.                
    last(Arities, (ArityMaxi,Source)),
    HRepairs = arityChange(Predicate, ArityMaxi),
    findall((Sentence,SS), 
        (((member((Sentence,SS), AllSents), member(+[Predicate|Args], Sentence));
          (member((Sentence,SS), AllSents), member(-[Predicate|Args], Sentence))),
          length(Args, L), 
          L<ArityMaxi),
          ToReSents),     % Get all sentences which has the predicate but with smaller arity.
    subtract(AllSents, ToReSents, RestSents),
    arityIncrease(Predicate, ArityMaxi, ToReSents, HRSents), % Delete the extra arguments in ToReSents, we get HRSents.
    substitute((Predicate, Arities), Signature, (Predicate, [(ArityMaxi,Source)]), NewSigTem),  % update signature by replacing (Predicate, Arities) with (Predicate, [(ArityMaxi,Source)])
    concepChange(T, RestSents, TRSents, TRepairs, NewSigTem, NewSig),
    append(HRSents, TRSents, RSents).




arityReduce(_, _, [], []):- !.
arityReduce(Predicate, ArityMini, [HSent|T], [HRepSent| TRepSents]):- 
    (member(+[Predicate|Args], HSent)->
    split_at(ArityMini, Args, ArguSaved, _),
    substitute(+[Predicate|Args], HSent, +[Predicate|ArguSaved], HRepSent);  % update the Clause by replacing the proposition +[Predicate|Args] with  +[Predicate|Arguments].
     
    member(-[Predicate|Args], HSent),
    split_at(ArityMini, Args, ArguSaved, _),
    substitute(-[Predicate|Args], HSent, +[Predicate|ArguSaved], HRepSent)),  % update the Clause by replacing the proposition +[Predicate|Args] with  +[Predicate|Arguments].
    
    arityReduce(Predicate, ArityMini, T, TRepSents).
    


arityIncrease(_, _, [], []):- !.
arityIncrease(Predicate, ArityMaxi, [HSent|T], [HRepSent| TRepSents]):- 
    (member(+[Predicate|Args], HSent)->
     length(Args, L1),
     L2 is ArityMaxi - L1,
     length(NewArgus, L2),
     maplist(=([dummy]), NewArgus),                     % add dummy0 as the new arguments.
     append(Args, NewArgus, Arguments),
     substitute(+[Predicate|Args], HSent, +[Predicate|Arguments], HRepSent);  % update the Clause by replacing the proposition +[Predicate|Args] with  +[Predicate|Arguments].
     
     member(-[Predicate|Args], HSent),
     length(Args, L1),
     L2 is ArityMaxi - L1,
     length(NewArgus, L2),
     maplist(=(dummy0), NewArgus),
     append(Args, NewArgus, Arguments),
     substitute(-[Predicate|Args], HSent, -[Predicate|Arguments], HRepSent)),
     
    arityIncrease(Predicate, ArityMaxi, T, TRepSents).

    

