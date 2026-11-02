(** Federer (1969), 2.4.16, p. 90: measurability of the weight used in the
    sign-constrained tests. Source context: PositiveIntegrableWeightUP.v.
    This consequence depends only on the integral specification; the private
    series is never unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic ExtendedFiniteProjectionBorel NormPowerScalar
  MeasureUP MeasurableFunctionUP MeasurablePostcomposition MeasurableGraphEquivalence
  BorelFunctionBasic PositiveIntegrableWeightUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_integrable_weight_measurable]: supporting
    measurability of the weight in Federer 2.4.16, p. 90, derived
    from its finite integral without exposing the construction. *)
Lemma positive_integrable_weight_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (w : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_positive_integrable_weight mu A w ->
  is_measure_measurable_function mu (partial_function_total w).
Proof.
move=> hw; have [b [_ [_ hi]]] := positive_weight_integrable hw.
have hb := borel_function_composition (@extended_finite_projection_borel R)
  (continuous_borel_function (@real_scalar_norm_identity_continuous R)).
have hmapped := @measurable_function_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm _
  (fun z => (fine z : real_norm_metric_space (scalar_absolute_value_norm R))) hi.1 hb.
apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hmapped)=> x z; split.
- move=> [r [hr he]]; change (w x=z); by rewrite -(hr : (w x)%:E=r) in he.
- move=> hz; exists (w x)%:E; by split.
Qed.
