:- module(
  relation,
  [
    equiv/1, % +Relation:ugraph
    equiv_class/3, % +EquivalenceRelation:ugraph
                   % +Element
                   % -EquivalenceClass:ordset
    quotient_set/3, % +EquivalenceRelation:ugraph
                    % +Set:ordset
                    % -QuotientSet:ordset(ordset)
    reflexive/1, % +Relation:ugraph
    reflexive_closure/2, % +Relation:ugraph
                         % -ReflexiveRelation:ugraph
    relation/3, % ?Relation:ugraph
                % ?Set:ordset
                % ?Pairs:ordset(pair)
    relation_pair/2, % +Relation:ugraph
                     % ?Pair:pair
    symmetric/1, % +Relation:ugraph
    symmetric_closure/2, % +Relation:ugraph
                         % -SymmetricRelation:ugraph
    transitive/1 % +Relaton:ugraph
  ]
).

/** <module> Relation

Support for properties of relations.

@author Wouter Beek
@license MIT license
@version 2015/10
*/

:- use_module(library(aggregate)).
:- use_module(library(closure)).
:- use_module(library(graph/graph_test)).
:- use_module(library(graph/s/s_edge)).
:- use_module(library(graph/s/s_graph)).
:- use_module(library(lambda)).
:- use_module(library(lists)).
:- use_module(library(pair_ext)).

:- meta_predicate(relational_closure(+,2,-)).





%! equiv_class(
%!   +EquivalenceRelation:ugraph,
%!   +Element,
%!   -EquivalenceClass:ordset
%! ) is det.
% Returns the equivalence class of Element relative to
% the given EquivalenceRelation.
%
% The function that maps from elements onto their equivalence classes is
% sometimes called the *|canonical projection map|*.
%
% @arg EquivalenceRelation An binary relation that is reflexive,
%      symmetric and transitive, represented as a directed graph.
% @arg Element The element whose equivalence class is returned.
% @arg EquivalenceClass The equivalence class of `Element`.
%      This is an ordered set.

equiv_class(EqRel, X, EqClass):-
  closure(
    % Since an equivalence relation is symmetric,
    % we do not need to use e.g. adjacent/3 here.
    \X^Y^relation_pair(EqRel, X-Y),
    [X],
    EqClass
  ).

:- begin_tests('equiv_class/3').

test(
  'equiv_class(+,+,-) is det. TRUE',
  [forall(equiv_class_test(GName,X,EqClass))]
):-
  test_graph(GName, EqRel)
  equiv_class(EqRel, X, EqClass).

equiv_class_test(equiv(1), 1, [1,2,3,4]).
equiv_class_test(equiv(1), 2, [1,2,3,4]).
equiv_class_test(equiv(1), 3, [1,2,3,4]).
equiv_class_test(equiv(1), 4, [1,2,3,4]).

:- end_tests('equiv_class/3').



%! is_equiv(+Relation:ugraph) is semidet.
% Succeeds if the given relation is an equivalence relation.

is_equiv(Rel):-
  is_reflexive(Rel),
  is_symmetric(Rel),
  is_transitive(Rel).



%! is_reflextive(+Relation:ugraph) is semidet.
% Succeeds if the given binary relation is reflexive.

is_reflexive(Rel):-
  forall(
    member(X-Ns, Rel),
    memberchk(X, Ns)
  ).



%! is_symmetric(+Relation:ugraph) is semidet.
% Succeeds if the given relation is symmetric.

is_symmetric(Rel):-
  forall(
    relation_pair(Rel, X-Y),
    relation_pair(Rel, Y-X)
  ).



%! is_transitive(+Relation:ugraph) is semidet.
% Suceeds if the given binary relation is transitive.

is_transitive(Rel):-
  forall(
    (
      relation_pair(Rel, X-Y),
      relation_pair(Rel, Y-Z)
    ),
    relation_pair(Rel, X-Z)
  ).



%! quotient_set(
%!   +EquivalenceRelation:ugraph,
%!   +Set:ordset,
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
% @arg EquivalenceRelation A (binary) equivalence relation.
%      Represented as a directed graph (see [ugraph]).
% @arg Set An ordered set.
% @arg QuotientSet The quotient set of `Set`.
%      An ordered set.
%
% @tbd Use the algorithm for calculating graph components for this?

quotient_set(EqRelation, Set, QSet):-
  aggregate_all(
    set(EqClass),
    (
      member(X, Set),
      equiv_class(X, EqRel, EqClass)
    ),
    QSet
  ).



%! reflexive_closure(+Relation:ugraph, -ReflexiveRelation:ugraph) is det.

reflexive_closure(Rel, ReflRel):-
  relational_closure(
    Rel,
    \Pairs^Result^(
      member(Pair, Pairs),
      (   Result = Pair
      ;   pair_element(Pair, X),
          Result = X-X
      )
    ),
    ReflRel
  ).



%! relation(+Relation:ugraph, -Set:ordset, -Pairs:ordset(pair)) is det.
%! relation(-Relation:ugraph, +Set:ordset, +Pairs:ordset(pair)) is det.
% Succeeds if Relation relates the elements in Set according to Pairs.

relation(Rel, Set, Pairs):-
  s_graph_components(Rel, Set, Pairs).



%! relation_pair(+Relation:ugraph, +Pair:pair) is semidet.
%! relation_pair(+Relation:ugraph, -Pair:pair) is nondet.
% The extension of a binary relation.

relation_pair(Rel, Pair):-
  s_edge(Rel, Pair).



%! symmetric_closure(+Relation:ugraph, -SymmetryRelation:ugraph) is det.

symmetric_closure(Rel, SymmRel):-
  relational_closure(
    Rel,
    \Pairs^Result^(
      member(Pair, Pairs),
      (   Result = Pair
      ;   inverse_pair(Pair, Result)
      )
    ),
    SymmRel
  ).



%! transitive_closure(+Relation:ugraph, -TransitiveRelation:ugraph) is det.
% Transitive closure over a srep graph / ugraph could have been implemented
% using relational_closure/3:

transitive_closure(Rel, TransRel):-
  relational_closure(
    Rel,
    \Pairs^Result^(
        member(Result, Pairs)
    ;   member(X-Y, Pairs),
        member(Y-Z, Pairs),
        Result = X-Z
    ),
    TransRel
  ).





% HELPERS %

%! relational_closure(
%!   +Relation:ugraph,
%!   :Goal,
%!   -ClosedRelation:ugraph
%! ) is det.
% Allows the calculation of the closure of a relation directly.
% Internally, the closure is calculated for the extension of the relation,
% i.e., its edge pairs.
%
% The mode is the same as for `Goal`.

relational_closure(Rel, Goal_2, ClosedRel):-
  relation(Rel, Set, Pairs),
  closure(Goal_2, Pairs, ClosedPairs),
  relation(ClosedRel, Set, ClosedPairs).
