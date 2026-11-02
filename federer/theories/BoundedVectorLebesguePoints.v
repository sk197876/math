(** Federer (1969), 2.9.22, p. 168: almost every x belongs to the Lebesgue
    set of the bounded measurable vector field v, by 2.9.9, pp. 156–157.
    This application proves its local finite norm-integral hypothesis on
    every bounded measurable set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension
  MeasureUP MeasurableFunctionUP MeasureAlmostUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureDerivationContext ScalarLebesgueBallContext
  ScalarIntervalDerivationContext LebesgueScalarMeasure MeasureLebesgueSet NormedLebesguePoints
  SummableRealFunctionUP BoundedVectorNormSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_vector_lebesgue_points_ae]: direct
    supporting application of 2.9.9 in Federer 2.9.22,
    p. 168. Every bounded measurable map into a separable
    normed space has conull Lebesgue set for the printed
    nondegenerate-interval relation. The finite local norm
    integrals are derived, not assumed separately. *)
Theorem bounded_vector_lebesgue_points_ae (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (C : set (real_norm_metric_space hN))
    (v : real_line_metric R -> real_norm_metric_space hN) (L : R) :
  countable C -> dense C ->
  is_measure_measurable_function (@lebesgue_scalar_measure R) (partial_function_total v) ->
  (forall x, N (v x)<=L) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    (@measure_lebesgue_set R [the metricType R of real_line_metric R]
      [the metricType R of real_norm_metric_space hN]
      (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)
      (partial_function_total v)).
Proof.
move=> hCc hCd hv hb.
have hm := lebesgue_scalar_is_measure R.
apply: (@federer_2_9_9 R [the metricType R of real_line_metric R] E N hN
  (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)
  (partial_function_total v) C (scalar_interval_derivation_context R) hv hCc hCd).
move=> A hAb hAm.
have hfinite := derivation_measure_bounded_finite (scalar_lebesgue_derivation_class R) hAb.
have hAf : (@lebesgue_scalar_measure R) A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hmass : (@lebesgue_scalar_measure R) A=(fine ((@lebesgue_scalar_measure R) A))%:E.
  by rewrite fineK.
have [J hJ] := @bounded_vector_norm_subset_integral R (real_line_metric R) E N hN C
  (@lebesgue_scalar_measure R) hm A (fine ((@lebesgue_scalar_measure R) A)) L v
  hCc hCd hAm hmass hv hb.
exists J.
apply: (@measure_integral_graph_equivalent R (real_line_metric R)
  (@lebesgue_scalar_measure R) _ _ J%:E _ hJ)=> x y.
rewrite !partial_function_zero_extension_graph; split.
- move=> [[hx he]|hx]; last by right.
  left; split=> //; exists (v x); split=> //.
  exact: (real_total_integrand_graph _ _ _).1 he.
- move=> [[hx [z [hz he]]]|hx]; last by right.
  left; split=> //; apply/real_total_integrand_graph.
  by rewrite (hz : v x=z).
Qed.
