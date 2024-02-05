

axiom([+contains(alert_medics, image_data)]).
axiom([+requires(personal_data, legal_basis)]).
axiom([+requires(consent, active_opt_in)]).
axiom([+instance_of(image_data, personal_data)]).
axiom([+instance_of(consent, legal_basis)]).
axiom([+instance_of(contract, legal_basis)]).
axiom([+instance_of(legal_obligation, legal_basis)]).
axiom([+instance_of(vital_interests, legal_basis)]).
axiom([+instance_of(public_task, legal_basis)]).
axiom([+instance_of(legitimate_interests, legal_basis)]).
axiom([-threat_to_life(\c), +grounds_for_processing(\c, vital_interests, personal_data)]).
axiom([-collision(\c),+airbag_deploy(\c)]).
axiom([-collision(\c), -consent(\c), +alert_medics(\c)]).
axiom([-contains(\need, \x), -require(\x, legal_basis), -instance_of(\w, legal_basis), -grounds_for_processing(\z, \w, \x), +act_on(\z, \need)]).
axiom([+collision(car)]).
:- working_directory(_, '/Users/xueli/Documents/code/cogAI_legal/ABC_Datalog-main/code').
:-[main].

trueSet([collision(car), airbag_deploy(car), act_on(car, alert_medics)]).
falseSet([]).


heuristics([ noAxiomDele, noReform, noVabWeaken, noPrecDele]).


