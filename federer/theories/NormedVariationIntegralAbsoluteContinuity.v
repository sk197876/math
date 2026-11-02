(** Federer (1969), 2.9.22, pp. 167–168: equivalence of the norm
    variation-integral equality and finite-family absolute continuity,
    extending 2.9.20(2)<=>2.9.20(3), pp. 165–166. Use the proved N(g')=s'
    almost everywhere and the metric finite-family refinement; the original
    scalar corollary applies to the actual arc-length parameter. No relevant
    erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CurveArcLength CurveVariationUP
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands NormedBVDerivativeIntegral
  NormedCurveAbsoluteContinuityUP MetricCurveAbsoluteContinuityUP MetricAbsoluteContinuityArcLength
  RealAbsoluteContinuityUP RealAbsoluteContinuity StieltjesMonotone StieltjesImageMeasures
  RealCurveDerivativeIntegrands MeasureUP MeasureAlmostUP MeasureAlmostEquality
  MeasureDensityTransfer MeasureIntegralAlmostEquality MeasureSubsetIntegral
  LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_variation_integral_equality_arc]: supporting
    normed/scalar equivalence in Federer 2.9.22, pp. 167–168,
    extending condition (2) of 2.9.20, p. 165. The actual norm
    integrand agrees almost everywhere with |s'|; scalar arc-length
    variation equals the original vector variation. Both directions
    retain the actual subset integral and its precise value. *)
Lemma normed_variation_integral_equality_arc (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a b : R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] -> a<=b ->
  (normed_curve_variation_integral_equality hN g a b <->
    real_curve_variation_integral_equality (arc_length g) a b).
Proof.
move=> hg he hab.
have hs (u v : R) : u<=v -> arc_length g u<=arc_length g v :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg u v.
have hVar : curve_variation (arc_length g : R -> real_line_metric R) a b=curve_variation g a b.
  by rewrite (@monotone_curve_variation_eq R (arc_length g) hs a b hab)
    (@arc_length_increment R [the metricType R of real_norm_metric_space hN] g hg a b hab).
have hAE := @normed_bv_norm_arc_derivative_almost_equal R E N hN g hg he.
have hA := @zero_extension_almost_equal R (real_line_metric R) _ (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) 0%E `[a,b] _ _ hAE.
rewrite /normed_curve_variation_integral_equality /real_curve_variation_integral_equality hVar.
split=> hi.
- exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ (curve_variation g a b) hi hA).
- exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ (curve_variation g a b) hi (measure_almost_equal_sym hA)).
Qed.

(** Source for [normed_variation_integral_equality_absolute_continuity]:
    direct (2)<=>(3) part of the extension in Federer 2.9.22,
    pp. 167–168, of 2.9.20, pp. 165–166. Apply the proved
    scalar corollary to arc length, then the metric finite-family
    equivalence. Actual norm derivative existence almost everywhere
    is an explicit intermediate premise supplied by the proved
    reflexive Banach theorem. No new differentiability axiom appears. *)
Theorem normed_variation_integral_equality_absolute_continuity (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a b : R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] -> a<b ->
  (normed_curve_variation_integral_equality hN g a b <->
    is_absolutely_continuous_metric_curve g a b).
Proof.
move=> hg he hab.
have hs (u v : R) : u<=v -> arc_length g u<=arc_length g v :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg u v.
have hfin := @monotone_locally_finite_variation R (arc_length g) hs.
have [psip [psim hp]] := @induced_measure_pair_exists R (arc_length g) hfin.
have hCor := @federer_2_9_20 R (arc_length g) psip psim a b hfin hp hab.
have hArc := @metric_absolute_continuity_arc_length R [the metricType R of real_norm_metric_space hN]
  g a b hg.
have hEq := @normed_variation_integral_equality_arc R E N hN g a b hg he (ltW hab).
split.
- move=> h2; exact (hArc.2 (hCor.2.1.1 (hEq.1 h2))).
- move=> h3; exact (hEq.2 (hCor.2.1.2 (hArc.1 h3))).
Qed.
