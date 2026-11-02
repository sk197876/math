(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPostcomposition MeasurableFunctionUP MeasureUP MeasureAlmostUP
  MeasureSubsetIntegral MeasureIntegralGraphEquivalence PartialZeroExtension
  MeasurableDistanceTo MeasureDerivationContext CoveringFamilyUP MeasureLebesgueSet MetricLebesguePoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_9_9]: direct complete corollary Federer 2.9.9, pp.
    156–157: the Lebesgue set of a measurable function into a separable
    normed vector space is conull when its norm has finite integral on every
    bounded measurable set. The norm is specified by laws and no
    completeness or finite-dimensional hypothesis is added. we retain p=1. *)
Theorem federer_2_9_9 (R : realType) (X : metricType R) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (real_norm_metric_space hN)) (D : set (real_norm_metric_space hN)) :
  is_measure_derivation_context phi V -> is_measure_measurable_function phi f ->
  countable D -> dense D ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A
      (partial_function_postcompose f (fun v => ((N v)%:E : extended_real_line R))) a%:E) ->
  measure_almost_everywhere phi (measure_lebesgue_set phi V f).
Proof.
move=> hc hf hDc hDd hlocal.
apply: (@metric_lebesgue_points_almost_everywhere R X
  [the metricType R of real_norm_metric_space hN] phi V f 0%R D hc hf hDc hDd).
move=> A hAb hAm; have [a ha] := hlocal A hAb hAm; exists a.
apply: (@measure_integral_graph_equivalent R X phi _ _ a%:E _ ha)=> x z.
rewrite !partial_function_zero_extension_graph; split.
- move=> [[hx [v [hv he]]]|hx]; last by right.
  left; split=> //; exists v; split=> //.
  by rewrite real_norm_metric_distanceE subr0.
- move=> [[hx [v [hv he]]]|hx]; last by right.
  left; split=> //; exists v; split=> //.
  by move: he; rewrite real_norm_metric_distanceE subr0.
Qed.
