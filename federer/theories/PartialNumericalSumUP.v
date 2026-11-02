(** Federer (1969), 2.4.8, p. 84: the pointwise sum of a countable family of
    nonnegative measurable functions, with numerical summation as defined in
    2.1.1, pp. 51–53. We specify the graph through the existing
    numerical-sum laws. This supporting specification also admits signed
    families exactly at points where the numerical sum is defined; no value
    is assigned to infinity minus infinity or outside a summand's domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_partial_function_numerical_sum]: abstract
    graph specification for the pointwise sum in Federer
    2.4.8, p. 84, using the defined numerical sums
    of 2.1.1, pp. 51–53. *)
Definition is_partial_function_numerical_sum (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :=
  forall x z, partial_function_graph g x z <-> exists u : J -> \bar R,
    (forall j, D j -> partial_function_graph (f j) x (u j)) /\ numerical_sum D u = Some z.

(** Source for [partial_numerical_sum_graph_unique]: supporting
    uniqueness of the pointwise sum graph in Federer 2.4.8,
    p. 84, including its partial domain. *)
Lemma partial_numerical_sum_graph_unique (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum D f g -> is_partial_function_numerical_sum D f h ->
  forall x z, partial_function_graph g x z <-> partial_function_graph h x z.
Proof. by move=> hg hh x z; rewrite (hg x z) (hh x z). Qed.
