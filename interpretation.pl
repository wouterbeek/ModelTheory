:- module(
  interpretation,
  [
    add_interpretation/2, % +Term:compound
                          % +Interpretation
    evaluate_formula/1, % +Formula:compound
    interpretation/2 % ?Term:compound
                     % ?Interpretation
  ]
).

/** <module> Interpretation

Implements the interpretation of formulas from a formal language
into the universe of discourse.

@author Wouter Beek
@version 2014/07
*/

:- use_module(library(apply)).
:- use_module(library(plunit)).

:- use_module(generics(db_ext)).

:- use_module(plSet(universe_of_discourse)).

:- use_module(plMt(formal_language)).

:- dynamic(interpretation/2).



¬(Goal):-
  \+ evaluate_formula(Goal).


∧(Goal1, Goal2):-
  evaluate_formula(Goal1),
  evaluate_formula(Goal2).


∨(Goal1, _):-
  evaluate_formula(Goal1), !.
∨(_, Goal2):-
  evaluate_formula(Goal2).


⊕(Goal1, Goal2):-
  evaluate_formula(Goal1), !,
  \+ evaluate_formula(Goal2).
⊕(Goal1, Goal2):-
  \+ evaluate_formula(Goal1),
  evaluate_formula(Goal2).


→(Goal1, Goal2):-
  evaluate_formula(Goal1),
  evaluate_formula(Goal2).


↔(Goal1, Goal2):-
  evaluate_formula(→(Goal1, Goal2)),
  evaluate_formula(→(Goal2, Goal1)).


%! add_interpretation(+Term:compound, +Interpretation) is det.
% Succeeds if the given term already has the given interpretation.
%
% @throws existence_error if `Term` does not denote an expression
%         in the current formal language.
% @throws instantiation_error if `Term` is uninstantiated.
% @throws instantiation_error if `Interpretation` is uninstantiated.

% Error: `Term` uninstantiated.
add_interpretation(Term, _):-
  var(Term), !,
  instantiation_error(Term).
% Error: `Interpretation` uninstantiated.
add_interpretation(_, Interpretation):-
  var(Interpretation), !,
  instantiation_error(Interpretation).
% Interpretation of an individual constant.
add_interpretation(IndividualConstant, Object):-
  individual_constant(IndividualConstant), !,
  add_interpretation_individual_constant0(IndividualConstant, Object).
% Interpretation of a predicate symbol.
add_interpretation(Predicate, Relation):-
  predicate(Predicate), !,
  add_interpretation_predicate0(Predicate, Relation).
% Error: `Term` does not exist.
add_interpretation(Term, _):-
  existence_error(term, Term).

% Error: object does not exist.
add_interpretation_individual_constant0(_, Object):-
  \+ object(Object), !,
  existence_error(object, Object).
% Add the individual constant interpretation.
add_interpretation_individual_constant0(IndividualConstant, Object):-
  db_add_novel(interpretation(IndividualConstant/0, Object)).

% Error: relation does not exist.
add_interpretation_predicate0(_, Relation):-
  \+ relation(Relation), !,
  existence_error(relation, Relation).
% Add the predicate interpretation.
add_interpretation_predicate0(Predicate, Relation):-
  db_add_novel(interpretation(Predicate, Relation)).


%! evaluate_formula(+Formula:compound) is semidet.

evaluate_formula(AtomicFormula):-
  atomic_formula(AtomicFormula), !,
  compound_name_arguments(AtomicFormula, Predicate, Arguments),
  maplist(interpretation, [Predicate|Arguments], [Relation|Objects]),
  once(relation(Relation, Objects)).
evaluate_formula(Formula):-
  Formula.

:- begin_tests(evaluate_formula).

test(
  'evaluate_formula(+) is semidet. TRUE',
  [
    forall(evaluate_formula_test(Formula, true)),
    setup(load_i1)
  ]
):-
  evaluate_formula(Formula).

evaluate_formula_test(⊕(dachshund(wouter),dachshund(teddy)), true).

:- end_tests(evaluate_formula).


%! interpretation(+Name:atom, +Object) is semidet.
%! interpretation(+Name:atom, -Object) is semidet.
%! interpretation(-Name:atom, +Object) is nondet.
%! interpretation(-Name:atom, -Object) is multi.
% @tbd Add support for functions.



% Debug.

load_i1:-
  formal_language:load_fl1([C1,C2,C3], [P1,P2]),
  universe_of_discourse:load_uod1([O1,O2,O3], [R1,R2]),
  maplist(add_interpretation, [C1,C2,C3,P1,P2], [O1,O2,O3,R1,R2]).

