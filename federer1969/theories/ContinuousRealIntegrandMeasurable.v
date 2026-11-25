(** Supporting measurable tests in Federer (1969), 2.9.21, p. 166, using the
    Borel inverse-image facts of 2.3.2, p. 73. Only the existing
    general-topology and finite-embedding laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasureAlmostBasic
  BorelRegularMeasureUP BorelFunctionBasic MeasurableFunctionUP MeasurableGraphEquivalence
  MeasurableRealEmbedding SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_real_integrand_measurable]: supporting
    measurability for the 2.4.10 calculation in Federer 2.9.21, p. 166 A
    continuous finite real function is measurable for any Borel regular
    measure, including its actual extended-real embedding. *)
Lemma continuous_real_integrand_measurable (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (f : X -> R) : is_measure mu ->
  is_borel_regular_measure mu -> continuous (f : X -> real_line_metric R) ->
  is_measure_measurable_function mu (real_total_integrand f).
Proof.
move=> hm hr hf.
have ht : is_measure_measurable_function mu (partial_function_total (f : X -> real_line_metric R)).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
  - move=> U hU; rewrite partial_function_total_preimage.
    exact (@borel_regular_borel_measurable R X mu hm hr _
      (@continuous_borel_function X [the topologicalType of real_line_metric R] f hf U hU)).
have hi := @measurable_total_real_embedding R X mu hm f ht.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hi)=> x z.
by rewrite real_total_integrand_graph.
Qed.
