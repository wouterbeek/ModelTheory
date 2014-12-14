:- module(
  relation,
  [
    equivalence/1, % +Relation:ugraph
    equivalence_class/3, % +Element
                         % +EquivalenceRelation:ugraph
                         % -EquivalenceClass:ordset
    quotient_set/3, % +Set:ordset
                    % +EquivalenceRelation:ugraph
                    % -QuotientSet:ordset(ordset)
    reflexive/1, % +Relation:ugraph
    reflexive_closure/2, % +Relation:ugraph
                         % -ReflexiveRelation:ugraph
    relation/3, % ?Relation:ugraph
                % ?Set:ordset
                % ?Pairs:ordset(pair)
    relation_element/2, % +Relation:ugraph
                        % ?Element
    relation_pair/2, % +Relation:ugraph
                     % ?Pair:pair
    symmetric/1, % +Relation:ugraph
    symmetric_closure/2, % +Relation:ugraph
                         % -SymmetricRelation:ugraph
    transitive/1 % +Relaton:ugraph
  ]
).
:- reexport(
  plGraph(graph_srep),
  [
    transitive_closure/2 % +Graph:ugraph
                         % -Closure:ugraph
  ]
).

/** <module> Relation

Support for properties of relations.

@author Wouter Beek
@version 2012/11, 2013/08, 2014/08, 2014/10-2014/11
*/

:- use_module(library(aggregate)).
:- use_module(library(lists), except([delete/3,subset/2])).

:- use_module(generics(closure)).
:- use_module(generics(lambda_meta)).
:- use_module(generics(pair_ext)).
:- use_module(pl(pl_mode)).

:- use_module(plSet(set_theory)).

:- use_module(plGraph(graph_edge)).
:- use_module(plGraph(s_graph/s_graph)).

:- meta_predicate(relational_closure(+,2,-)).



%! equivalence(+Relation:ugraph) is semidet.
% Succeeds if the given relation is an equivalence relation.

equivalence(Relation):-
  reflexive(Relation),
  symmetric(Relation),
  transitive(Relation).


%! equivalence_class(
%!   +EquivalenceRelation:ugraph,
%!   +Element,
%!   -EquivalenceClass:ordset
%! ) is det.
% Returns the equivalence class of =X= relative to equivalence relation =R=.
%
% The function that maps from elements onto their equivalence classes is
% sometimes calles the *|canonical projection map|*.
%
% @arg Element The element whose equivalence class is returned.
% @arg Equivalence An binary equivalence relation,
%      i.e., a relation that is:
%        1. Reflexive
%        2. Symmetric
%        3. Transitive
%      Represented as a directed graph (see [ugraph]).
% @arg EquivalenceClass The equivalence class of `Element`.
%      This is an ordered set.

equivalence_class(Element, EquivalenceRelation, EquivalenceClass):-
  closure(
    % Since an equivalence relation is symmetric,
    % we do not need to use e.g. adjacent/3 here.
    \Element^EquivalentElement^(
      relation_pair(EquivalenceRelation, Element-EquivalentElement)
    ),
    [Element],
    EquivalenceClass
  ).


%! quotient_set(
%!   +Set:ordset,
%!   +EquivalenceRelation:ugraph,
%!   -QuotientSet:ordset(ordset)
%! ) is det.
% Returns the quotient set for `Set`,
% closed under equivalence relation `EquivalenceRelation`.
%
% The quotient set of a set `Set` is the set of all equivalence sets of
% elements in `Set`.
%
% A quotient set of `Set` is also a partition of `Set`.
%
% The standard notation for a quotient set is $S / \approx$.
%
% @arg Set An ordered set.
% @arg EquivalenceRelation A (binary) equivalence relation.
%      Represented as a directed graph (see [ugraph]).
% @arg QuotientSet The quotient set of `Set`.
%      An ordered set.
%
% @tbd Use the algorithm for calculating graph components for this?

quotient_set(Set, EquivalenceRelation, QuotientSet):-
  aggregate_all(
    set(EquivalenceClass),
    (
      member(Element, Set),
      equivalence_class(Element, EquivalenceRelation, EquivalenceClass)
    ),
    QuotientSet
  ).


%! reflextive(+Relation:ugraph) is semidet.
% Succeeds if the given binary relation is reflexive.

reflexive(Relation):-
  forall(
    member(X-Ns, Relation),
    memberchk(X, Ns)
  ).


%! reflexive_closure(+Relation:ugraph, -ReflexiveRelation:ugraph) is det.

reflexive_closure(Relation, ReflexiveRelation):-
  relational_closure(
    Relation,
    \Pairs^Result^(
      member(Pair, Pairs),
      (
        Result = Pair
      ;
        pair_element(Pair, Element),
        Result = Element-Element
      )
    ),
    ReflexiveRelation
  ).


%! relation(+Relation:ugraph, -Set:ordset, -Pairs:ordset(pair)) is det.
%! relation(-Relation:ugraph, +Set:ordset, +Pairs:ordset(pair)) is det.

relation(Relation, Set, Pairs):-
  graph_components(Relation, Set, Pairs).


%! relation_element(+Relation:ugraph, +Element) is semidet.
%! relation_element(+Relation:ugraph, -Element) is nondet.

relation_element(Relation, Element):-
  call_ground_as_semidet(member(Element-_, Relation)).


%! relation_pair(+Relation:ugraph, +Pair:pair) is semidet.
%! relation_pair(+Relation:ugraph, -Pair:pair) is nondet.
% The extension of a binary relation.

relation_pair(Relation, Pair):-
  edge(Relation, Pair).


%! symmetric(+Relation:ugraph) is semidet.
% Succeeds if the given relation is symmetric.

symmetric(Relation):-
  forall(
    relation_pair(Relation, X-Y),
    relation_pair(Relation, Y-X)
  ).


%! symmetric_closure(+Relation:ugraph, -SymmetryRelation:ugraph) is det.

symmetric_closure(Relation, SymmetryRelation):-
  relational_closure(
    Relation,
    \Pairs^Result^(
      member(Pair, Pairs),
      (
        Result = Pair
      ;
        inverse_pair(Pair, Result)
      )
    ),
    SymmetryRelation
  ).


%! transitive(+Relation:ugraph) is semidet.
% Suceeds if the given binary relation is transitive.

transitive(Relation):-
  forall(
    (
      relation_pair(Relation, X-Y),
      relation_pair(Relation, Y-Z)
    ),
    relation_pair(Relation, X-Z)
  ).


/* Transitive closure over a srep graph / ugraph could have been implemented
   using relational_closure/3:
%! transitive_closure(+Relation:ugraph, -TransitiveRelation:ugraph) is det.

transitive_closure(Relation, TransitiveRelation):-
  relational_closure(
    Relation,
    \Pairs^Result^(
      member(Result, Pairs)
    ;
      member(X-Y, Pairs),
      member(Y-Z, Pairs),
      Result = X-Z
    ),
    TransitiveRelation
  ).
*/



% Helpers.

%! relational_closure(
%!   +Relation:ugraph,
%!   :Goal,
%!   -ClosedRelation:ugraph
%! ) .
% Allows the calculation of the closure of a relation directly.
% Internally, the closure is calculated for the extension of the relation,
% i.e., its edge pairs.
%
% The mode is the same as for `Goal`.

relational_closure(Relation, Goal, ClosedRelation):-
  relation(Relation, Set, Pairs),
  closure(Goal, Pairs, ClosedPairs),
  relation(ClosedRelation, Set, ClosedPairs).

