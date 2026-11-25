(** Federer (1969), 3.1.4, p. 214: scalar reduction of the
    approximate partial derivative. The absolute-value norm topology
    and the ordinary real topology give the same approximate limits. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity
  RealMetricBackground ScalarNormExtendedEmbedding PartialFunctionUP
  PartialFunctionPostcomposition MeasureApproximateLimitUP
  ApproximateLimitComposition ApproximateLimitGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_scalar_norm_identity_continuous]: supporting
    inverse topology identification for the scalar case of Federer
    3.1.4, p. 214. Absolute-difference distances coincide. *)
Lemma real_scalar_norm_identity_continuous (R : realType) :
  continuous (fun x : real_line_metric R=>
    (x : real_norm_metric_space (scalar_absolute_value_norm R))).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=> x y.
change (`|x-y|<=1*`|x-y|); by rewrite mul1r.
Qed.

(** Source for [scalar_norm_approximate_limit_iff]: supporting exact
    agreement of scalar approximate limits in the first paragraph of
    proof of Federer 3.1.4, p. 214. Changing the presentation of the
    target preserves the function graph and its missing domain. *)
Lemma scalar_norm_approximate_limit_iff (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) x y :
  is_measure_approximate_limit mu V f x y <->
  @is_measure_approximate_limit R X [the topologicalType of real_line_metric R] mu V
    (partial_function_postcompose f (fun z=> (z : real_line_metric R))) x y.
Proof.
split=> hf.
- exact: approximate_limit_continuous_postcompose (@scalar_norm_real_identity_continuous R y) hf.
- have hh := @approximate_limit_continuous_postcompose R X
    [the topologicalType of real_line_metric R]
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu V
    (partial_function_postcompose f (fun z=>(z : real_line_metric R)))
    (fun z=>(z : real_norm_metric_space (scalar_absolute_value_norm R))) x y
    (@real_scalar_norm_identity_continuous R y) hf.
  apply: (@approximate_limit_graph_equivalent R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    mu V _ f x y _ hh)=> a b.
  split.
  + by move=> [u [[v [hv <-]] <-]].
  + by move=> hb; exists b; split=> //; exists b.
Qed.
