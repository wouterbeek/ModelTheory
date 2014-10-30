:- module(
  formal_language,
  [
    add_individual_constant/1, % +Name:atom
    add_predicate/1, % +Predicate:compound
    add_predicate/2, % +Name:atom
                     % +Arity:positive_integer
    algebraic_signature/1, % +Signature:compound
    atomic_formula/1, % ?Formula:compound
    formula/1 , % ?Formula:compound
    individual_constant/1, % ?Name:atom
    logical_connective/1, % ?Name:atom
    logical_connective/2, % ?Name:atom
                          % ?Arity:positive_integer
    op(900, fx,  ¬),
    op(900, xfy, ∧),
    op(900, xfy, ∨),
    op(900, xfy, ⊕),
    op(900, xfy, →),
    op(900, xfy, ↔),
    operator_depth/2, % +Formula:compound
                      % ?Depth:nonneg
    predicate/1, % ?Predicate:compound
    predicate/2, % ?Name:atom
                 % ?Arity:positive_integer
    relational_signature/1, % +Signature:compound
    signature/1, % -Signature:compound
    subformula/2, % ?Subformula:compound
                  % +Formula:compound
    term/1 % ?Term:compound
  ]
).

/** <module> Formal language

@author Wouter Beek
@tbd Add support for function symbols.
@version 2014/07
*/

:- use_module(library(aggregate)).
:- use_module(library(apply)).
:- use_module(library(error)).
:- use_module(library(lists), except([delete/3])).
:- use_module(library(pairs)).
:- use_module(library(plunit)).

:- use_module(generics(db_ext)).
:- use_module(generics(typecheck)).
:- use_module(math(math_ext)).

:- op(900, xf,  ¬). % U+00AC
:- op(900, xfx, ∧). % U+2227
:- op(900, xfx, ∨). % U+2228
:- op(900, xfx, ⊕). % U+2295
:- op(900, xfx, →). % U+2192
:- op(900, xfx, ↔). % U+2194

:- dynamic(individual_constant/1).

:- dynamic(logical_connective/2).

:- dynamic(predicate/2).



%! add_individual_constant(+Name:atom) is det.
% Adds the an individual constant to the current formal language.
%
% Succeeds if the given individual constant already exists.

add_individual_constant(Name):-
  var(Name), !,
  instantiation_error(Name).
add_individual_constant(Name):-
  db_add_novel(individual_constant(Name)).


%! add_predicate(+Predicate:compound) is det.
% Wrapper around add_predicate/2,
% supporting the Prolog predicate notation.
%
% @arg Predicate Uses the Prolog predicate notation `Name/Arity`.
%
% @throws instantiation_error if `Name` or `Arity` is uninstantiated.
% @throws type_error if `Arity` is not an integer.
% @throws domain_error if `Arity` is a negative integer or zero.

add_predicate(Name/Arity):-
  add_predicate(Name, Arity).


%! add_predicate(+Name:atom, +Arity:positive_integer) is det.
% Adds a predicate symbol to the current formal language.
%
% Succeeds if the given predicate already exists.
%
% Predicates with the same name but different arity are different predicates.
%
% @arg Name The atomic predicate symbol.
% @arg Arity The arity of the predicate symbol.
%      A positive integer.
%
% @throws domain_error if `Arity` is a negative integer or zero.
% @throws instantiation_error if `Name` or `Arity` is uninstantiated.
% @throws type_error if `Arity` is not an integer.

add_predicate(Name, _):-
  var(Name), !,
  instantiation_error(Name).
add_predicate(_, Arity):-
  var(Arity), !,
  instantiation_error(Arity).
add_predicate(_, Arity):-
  \+ integer(Arity), !,
  type_error(integer, Arity).
add_predicate(_, Arity):-
  \+ positive_integer(Arity), !,
  domain_error(positive_integer, Arity).
add_predicate(Name, Arity):-
  db_add_novel(predicate(Name, Arity)).


%! algebraic_signature(+Signature:compound) is semidet.
% Succeeds if the given signature contains no predicate symbols.
%
% Silently fails for non-signature arguments.
%
% @throws instantiation_error(Signature)

algebraic_signature(Signature):-
  var(Signature), !,
  instantiation_error(Signature).
algebraic_signature(signature([],[_|_],_)).


%! atomic_formula(+Formula:compound) is semidet.
%! atomic_formula(-AtomicFormula:compound) is nondet.
% ### Instantiation `(+)`
%
% Succeeds if the given formula is an atomic formula
% with respect to the current formal language.
%
% ### Instantiation `(-)`
%
% Enumerates the atomic formulas that can be built
% based on the current formal language.
%
% There are no quarantees on the order in which
% atomic formulas are returned.

% Check whether something is an atomic formula.
atomic_formula(Formula):-
  nonvar(Formula), !,

  % An atomic formula is a compound term with a specified arity.
  % For example, this excludes `loves(andrea,wouter,teddy)`.
  functor(Formula, Name, Arity),
  % This ensures that arity > 0.
  predicate(Name, Arity),

  % Make sure that all arguments are terms.
  % For example, this excludes `loves(dachshund(wouter),andrea)`.
  compound_name_arguments(Formula, Name, Terms),
  maplist(term, Terms).
% Generate an atomic formula.
atomic_formula(Formula):-
  predicate(Name, Arity),
  between(1, Arity, _),
  length(Arguments, Arity),
  maplist(term, Arguments),
  compound_name_arguments(Formula, Name, Arguments).

:- begin_tests(atomic_formula).

test(
  'atomic_formula(+) is semidet. TRUE',
  [
    forall(atomic_formula_test(AtomicFormula,true)),
    setup(load_fl1)
  ]
):-
  atomic_formula(AtomicFormula).
test(
  'atomic_formula(+) is semidet. FAIL',
  [
    fail,
    forall(atomic_formula_test(AtomicFormula,fail)),
    setup(load_fl1)
  ]
):-
  atomic_formula(AtomicFormula).
test(
  'atomic_formula(-) is nondet.',
  [
    set(AtomicFormula == [
      dachshund(andrea),
      dachshund(teddy),
      dachshund(wouter),
      loves(andrea,andrea),
      loves(andrea,teddy),
      loves(andrea,wouter),
      loves(teddy,andrea),
      loves(teddy,teddy),
      loves(teddy,wouter),
      loves(wouter,andrea),
      loves(wouter,teddy),
      loves(wouter,wouter)
    ]),
    setup(load_fl1)
  ]
):-
  atomic_formula(AtomicFormula).

atomic_formula_test(dachshund(andrea), true).
atomic_formula_test(dachshund(teddy), true).
atomic_formula_test(dachshund(wouter), true).
atomic_formula_test(loves(andrea,andrea), true).
atomic_formula_test(loves(andrea,teddy), true).
atomic_formula_test(loves(andrea,wouter), true).
atomic_formula_test(loves(teddy,andrea), true).
atomic_formula_test(loves(teddy,teddy), true).
atomic_formula_test(loves(teddy,wouter), true).
atomic_formula_test(loves(wouter,andrea), true).
atomic_formula_test(loves(wouter,teddy), true).
atomic_formula_test(loves(wouter,wouter), true).

atomic_formula_test(loves(dachshund(wouter),wouter), fail).
atomic_formula_test(wouter(dachshund), fail).
atomic_formula_test(andrea, fail).
atomic_formula_test(dachshund(teddy,teddy), fail).
atomic_formula_test(loves(andrea,wouter,teddy), fail).

:- end_tests(atomic_formula).


%! formula(+Formula:compound) is semidet.
%! formula(-Formula:compound) is nondet.

formula(Formula):-
  formula0(Formula, _).

%! formula0(+Formula:compound, +Depth:nonneg) is semidet.
%! formula0(+Formula:compound, -Depth:nonneg) is det.
%! formula0(-Formula:compound, +Depth:nonneg) is nondet.
%! formula0(-Formula:compound, -Depth:nonneg) is nondet.

% Atomic formulas have depth 0.
formula0(AtomicFormula, 0):-
  atomic_formula(AtomicFormula).
% Recursive case: unary logical connective.
formula0(Formula, Depth):-
  % If we do not perform this check, formula/2 will loop.
  (
    nonvar(Formula)
  ->
    % We cannot use compound_name_arguments/3 here,
    % since this would throw a type_error for
    % atomic instantiation of `Formula`.
    Formula =.. [UnaryConnective,Subformula]
  ;
    true
  ),

  % Make sure the logical connective is unary.
  logical_connective(UnaryConnective, 1),

  % Based on whether the operator depth is given,
  % we can generate the subformulas more/less efficient.
  (
    nonvar(Depth)
  ->
    succ(Subdepth, Depth),
    formula0(Subformula, Subdepth)
  ;
    formula0(Subformula, Subdepth),
    succ(Subdepth, Depth)
  ),

  % If we were not given a formula, we need to construct it
  % based on its subformulas.
  (
    var(Formula)
  ->
    compound_name_arguments(Formula, UnaryConnective, [Subformula])
  ;
    true
  ).
% Recursive case: binary logical connective.
formula0(Formula, Depth):-
  (
    nonvar(Formula)
  ->
    % We cannot use compound_name_arguments/3 here,
    % since this would throw a type_error for
    % atomic instantiation of `Formula`.
    Formula =.. [BinaryConnective|Subformulas]
  ;
    true
  ),

  logical_connective(BinaryConnective, 2),

  (
    nonvar(Depth)
  ->
    succ(Subdepth1, Depth),
    formula0(Subformula1, Subdepth1),
    betwixt(0, Subdepth1, Subdepth2),
    formula0(Subformula2, Subdepth2)
  ;
    formula0(Subformula1, Subdepth1),
    succ(Subdepth1, Depth),
    betwixt(0, Subdepth1, Subdepth2),
    formula0(Subformula2, Subdepth2)
  ),
  (
    Subformulas = [Subformula1,Subformula2]
  ;
    Subformulas = [Subformula2,Subformula1]
  ),

  (
    var(Formula)
  ->
    compound_name_arguments(Formula, BinaryConnective, Subformulas)
  ;
    true
  ).


%! individual_constant(+Name:atom) is semidet.
%! individual_constant(-Name:atom) is nondet.


%! logical_connective(+Name:atom) is semidet.
%! logical_connective(-Name:atom) is multi.

logical_connective(Name):-
  logical_connective(Name, _).

%! logical_connective(+Name:atom, +Arity:positive_integer) is semidet.
%! logical_connective(+Name:atom, -Arity:positive_integer) is semidet.
%! logical_connective(-Name:atom, +Arity:positive_integer) is nondet.
%! logical_connective(-Name:atom, -Arity:positive_integer) is multi.
% Dynamically asserted logical connectives.

logical_connective(¬, 1).
logical_connective(∧, 2).
logical_connective(∨, 2).
logical_connective(⊕, 2).
logical_connective(→, 2).
logical_connective(↔, 2).


%! operator_depth(+Formula:compound, +Depth:nonneg) is semidet.
%! operator_depth(+Formula:compound, -Depth:nonneg) is det.

operator_depth(Formula, Depth):-
  formula0(Formula, Depth).


%! predicate(+Predicate:compound) is semidet.
%! predicate(-Predicate:compound) is nondet.
% Wrapper around predicate/2,
% supporting the Prolog notation for predicates.

predicate(Name/Arity):-
  predicate(Name, Arity).


%! predicate(+Name, +Arity:positive_integer) is semidet.
%! predicate(+Name, -Arity:positive_integer) is nondet.
%! predicate(-Name, +Arity:positive_integer) is nondet.
%! predicate(-Name, -Arity:positive_integer) is nondet.
% Dynamically asserted predicate symbols.


%! relational_signature(+Signature:compound) is semidet.
% Succeeds if the given signature contains no function symbols.
%
% Silently fails for non-signature arguments.
%
% @throws instantiation_error(Signature)

relational_signature(Signature):-
  var(Signature), !,
  instantiation_error(Signature).
relational_signature(signature([_|_],[],_)).


%! signature(-Signature:compound) is det.
% Returns the signature of the current formal language.
%
% A signature has the following form
% ~~~{.pl}
% signature(
%   -Predicates:ordset(atom),
%   -FunctionSymbols:ordset(atom),
%   -ArityFunction:list(pair(atom,positive_integer))
% )
% ~~~
%
% @tbd Add support for function symbols.

signature(signature(Predicates,FunctionSymbols,ArityFunction)):-
  aggregate_all(
    set(Name-Arity),
    predicate(Name, Arity),
    ArityFunction
  ),
  FunctionSymbols = [],
  pairs_keys(ArityFunction, Predicates).


%! subformula(+Subformula:compound, +Formula:compound) is semidet.
%! subformula(-Subformula:compound, +Formula:compound) is multi.
% @throws instantiation_error if `Formula` is uninstantiated.
% @throws type_error if `Formula` is not a compound term.

subformula(_, Formula):-
  var(Formula), !,
  instantiation_error(Formula).
subformula(_, Formula):-
  \+ compound(Formula), !,
  type_error(compound, Formula).
% Generative case. Instantiation `(-,+)`.
subformula(Subformula, Formula):-
  var(Subformula), !,
  % Mode `nondet`: allow backtracking.
  subformula0(Subformula, Formula).
% Checking case. Instantiaion `(+,+)`.
subformula(Subformula, Formula):-
  % Enforse determinism after first result (if any).
  % Otherwise mode would be `nondet` rather than `semidet`.
  subformula0(Subformula, Formula), !.

% Base case.
subformula0(Formula, Formula).
% Recursive case.
subformula0(Subsubformula, Formula):-
  compound_name_arguments(Formula, Name, Subformulas),
  logical_connective(Name),
  member(Subformula, Subformulas),
  subformula0(Subsubformula, Subformula).

:- begin_tests(subformula).

test(
  'subformula(+,+) is semidet. TRUE',
  [
    forall(subformula_test(Subformula, Formula, true)),
    setup(load_fl1)
  ]
):-
  subformula(Subformula, Formula).

subformula_test(dachshund(teddy), dachshund(teddy), true).
subformula_test(⊕(dachshund(wouter),dachshund(teddy)), ⊕(dachshund(wouter),dachshund(teddy)), true).
subformula_test(dachshund(wouter), ⊕(dachshund(wouter),dachshund(teddy)), true).
subformula_test(dachshund(teddy), ⊕(dachshund(wouter),dachshund(teddy)), true).

:- end_tests(subformula).


%! term(+Term:compound) is semidet.
%! term(-Term:compound) is multi.

term(IndividualConstant):-
  individual_constant(IndividualConstant).



% Debug

load_fl1:-
  load_fl1(_, _).

load_fl1([andrea,teddy,wouter], [dachshund/1,loves/2]):-
  maplist(add_individual_constant, [andrea,teddy,wouter]),
  maplist(add_predicate, [dachshund/1,loves/2]).

