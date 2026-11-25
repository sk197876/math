(** Federer (1969), 2.10.24, p. 188, final paragraph: abstract supporting
    weighted-cover property for applying the Borel-partition theorem 2.10.8,
    p. 175. This predicate is a law to be proved for each cost; it
    introduces no project axiom. The actual Gross and integral-geometric
    inequalities have separate proofs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_weighted_borel_cover_bound]: supporting
    weighted-cover law for the final paragraph of 2.10.24,
    p. 188. An actual pointwise cover of a Borel target
    by countably many weighted Borel sets bounds its cost.
    Indices may repeat sets and all weights are finite
    nonnegative real numbers on the active index set. *)
Definition has_weighted_borel_cover_bound (R : realType) (X : topologicalType)
    (c : set X -> \bar R) :=
  forall (J : choiceType) (S : J -> set X) (G : set J) (u : J -> R) (A : set X),
    countable G -> (forall j, G j -> (0<=u j)%R) -> borel_set A ->
    (forall j, G j -> borel_set (S j)) ->
    (forall x, A x -> 1<=weighted_generator_sum S G u x) ->
    c A<=weighted_generator_cost (fun j=>c (S j)) G u.
