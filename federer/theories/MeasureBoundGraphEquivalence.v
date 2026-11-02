(** Federer (1969), proof of 2.4.4(3)–(6), p. 83: supporting substitution of
    numerical identities in upper and lower integral bounds. Exact graphs,
    including domains, must agree. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_integral_graph_equivalent]:
    supporting upper-bound substitution for the identities in
    Federer 2.4.4(3)–(6), p. 83. *)
Lemma measure_upper_integral_graph_equivalent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  measure_upper_integral mu f=measure_upper_integral mu g.
Proof.
move=> he; have [hu _] := measure_step_value_families_graph_equivalent mu he.
apply: (@measure_upper_integral_unique R X mu g).
- have h := measure_upper_integral_specification mu f.
  by rewrite /is_measure_upper_integral hu in h.
- exact: measure_upper_integral_specification.
Qed.

(** Source for [measure_lower_integral_graph_equivalent]:
    supporting lower-bound substitution for the identities in
    Federer 2.4.4(3)–(6), p. 83. *)
Lemma measure_lower_integral_graph_equivalent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  measure_lower_integral mu f=measure_lower_integral mu g.
Proof.
move=> he; have [_ hl] := measure_step_value_families_graph_equivalent mu he.
apply: (@measure_lower_integral_unique R X mu g).
- have h := measure_lower_integral_specification mu f.
  by rewrite /is_measure_lower_integral hl in h.
- exact: measure_lower_integral_specification.
Qed.
