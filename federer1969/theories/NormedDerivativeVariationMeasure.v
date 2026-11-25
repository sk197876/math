(** Federer (1969), 2.9.22, pp. 167–168: use the derivative variation
    measure of scalar arc length for the norm integrand in the extension of
    2.9.20, pp. 165–166. The proved equality s'=N(g') transfers its actual
    integral representation, while its null endpoints and segment bound
    follow from the scalar 2.9.19. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CurveArcLength CurveVariationUP
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands NormedBVDerivativeIntegral
  DerivativeVariationMeasure StieltjesMonotone StieltjesImageMeasures
  MeasureUP MeasureAlmostUP MeasureAlmostEquality MeasureDensityTransfer MeasureIntegralAlmostEquality
  MeasureSubsetIntegral LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_derivative_variation_measure_laws]: supporting
    norm-integral measure in Federer 2.9.22, pp. 167–168,
    extending the finite-family proof of 2.9.20, p. 166.
    Use the actual pair induced by arc length. Its continuous-part
    sum represents N(g') on every Lebesgue-measurable set, has null
    singletons and is bounded on segments by the original vector
    variation. No separate norm-variation measure is constructed. *)
Theorem normed_derivative_variation_measure_laws (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  is_induced_measure_pair (arc_length g) psip psim ->
  let nu := real_derivative_variation_measure psip psim in
  is_measure nu /\
  (forall A, measure_measurable (@lebesgue_scalar_measure R) A ->
    measure_measurable nu A /\ is_measure_subset_integral (@lebesgue_scalar_measure R)
      A (normed_curve_norm_derivative_integrand hN g) (nu A)) /\
  (forall x : R, nu [set x]=0%E) /\
  (forall a b : R, a<=b -> (nu `[a,b]<=curve_variation g a b)%E).
Proof.
move=> hg he hp nu.
have hs (a b : R) : a<=b -> arc_length g a<=arc_length g b :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg a b.
have hfin := @monotone_locally_finite_variation R (arc_length g) hs.
have [hm [hrep [hz hb]]] := @real_derivative_variation_measure_laws R (arc_length g) psip psim hfin hp.
have hEq := @normed_bv_norm_arc_derivative_almost_equal R E N hN g hg he.
split=> //; split.
- move=> A hA; split; first exact (hrep A hA).1.
  have hExt := @zero_extension_almost_equal R (real_line_metric R) _ (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) 0%E A _ _ (measure_almost_equal_sym hEq).
  exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ (nu A) (hrep A hA).2 hExt).
- split=> // a b hab.
  have h := hb a b hab.
  by rewrite (@monotone_curve_variation_eq R (arc_length g) hs a b hab)
    (@arc_length_increment R [the metricType R of real_norm_metric_space hN] g hg a b hab) in h.
Qed.
