(** Federer (1969), 2.9.22, pp. 167–168: extend the increment estimate in
    2.9.20(1)=>(2), p. 166. Apply the proved norm bound for the actual
    vector integral on a subsegment. Its L1 norm is the actual N(g')
    integral, represented by the scalar arc-length derivative variation
    measure. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP CurveArcLength
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands NormedCurveAbsoluteContinuityUP
  NormedPrimitiveSegmentIntegral NormedDerivativeVariationMeasure DerivativeVariationMeasure
  StieltjesImageMeasures PartialFunctionUP PartialNormPower RealPower
  MeasureVectorIntegralUP MeasureVectorIntegralBound MeasureLoneNormIntegral
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureRestriction RestrictedIntegralIdentity MeasureUP MeasureAlmostUP
  LebesgueScalarMeasure RealMetricBackground BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_primitive_increment_mass_bound]: supporting
    increment bound in Federer 2.9.22, pp. 167–168, extending
    2.9.20(1)=>(2), p. 166. Every subsegment increment norm is
    at most the actual derivative variation mass there. Compare two
    actual scalar integrals to identify the L1 norm, retaining exact
    powered-norm graphs at exponent one and null endpoints. *)
Lemma normed_primitive_increment_mass_bound (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN)
    (psip psim : set R -> \bar R) (a b u v : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists w : E, has_normed_curve_derivative N g x w] ->
  is_induced_measure_pair (arc_length g) psip psim ->
  normed_curve_indefinite_derivative_integral hN g a b -> a<=u -> u<=v -> v<=b ->
  ((N (g v-g u))%:E<=real_derivative_variation_measure psip psim `[u,v])%E.
Proof.
move=> hY hg he hp hF hau huv hvb.
have hL := lebesgue_scalar_is_measure R.
pose A : set (real_line_metric R) := `[u,v].
pose mu := measure_restrict (@lebesgue_scalar_measure R) A.
have hm := measure_restrict_is_measure hL A.
have hA : measure_measurable (@lebesgue_scalar_measure R) A.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R u v).
have hVec := @normed_indefinite_derivative_integral_subsegment R E N hN g a b u v
  hY hg he hF hau huv hvb.
have [_ [hrep _]] := @normed_derivative_variation_measure_laws R E N hN g psip psim hg he hp.
have hNorm := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL A _ _ hA).2 (hrep A hA).2.
have hLP := @measure_lone_norm_integral R (real_line_metric R) E N hN mu hm
  (normed_curve_derivative hN g) hVec.1.
have hGraph x y : partial_function_graph (partial_norm_power N 1%R (normed_curve_derivative hN g)) x y <->
    partial_function_graph (normed_curve_norm_derivative_integrand hN g) x y.
  rewrite normed_curve_norm_derivative_integrand_graph; split.
  - move=> [w [hw hwy]]; exists w; split=> //.
    by rewrite (@real_power_one_exponent R (N w) (real_seminorm_nonnegative hN.1 w)) in hwy.
  - move=> [w [hw hwy]]; exists w; split=> //.
    by rewrite (@real_power_one_exponent R (N w) (real_seminorm_nonnegative hN.1 w)).
have hLPnorm := @measure_integral_graph_equivalent R (real_line_metric R) mu _ _ _ hGraph hLP.
have hValue := measure_integral_unique hLPnorm hNorm.
have hBound := @measure_vector_integral_norm_bound R (real_line_metric R) E N hN mu hm
  (normed_curve_derivative hN g) (g v-g u) hVec.
by rewrite hValue in hBound.
Qed.
