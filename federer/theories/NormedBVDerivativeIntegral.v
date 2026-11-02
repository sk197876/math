(** Federer (1969), 2.9.22, pp. 167–168: extend the final norm-integral
    estimate of 2.9.19, pp. 164–165. The actual vector derivative norm
    agrees almost everywhere with the scalar absolute derivative of arc
    length. The proved scalar integral estimate therefore gives a finite
    actual norm integral bounded by the original variation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CurveArcLength CurveVariationUP
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands NormedBVVariationDerivative
  RealCurveDerivativeUP RealCurveDerivativeIntegrands RealBVDerivativeIntegral
  StieltjesMonotone StieltjesImageMeasures MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality MeasureDensityTransfer MeasureIntegralAlmostEquality
  MeasureSubsetIntegral LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_bv_norm_arc_derivative_almost_equal]: supporting
    integrand equality for Federer 2.9.22, pp. 167–168, extending
    the final display of 2.9.19, p. 165. The proved variation
    equality gives s'=N(g')>=0 on a common conull set, so the
    actual partial norm integrand agrees with |s'| there. *)
Lemma normed_bv_norm_arc_derivative_almost_equal (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  measure_almost_equal (@lebesgue_scalar_measure R)
    (normed_curve_norm_derivative_integrand hN g)
    (real_curve_absolute_derivative_integrand (arc_length g)).
Proof.
move=> hg he.
have hVar := @normed_bv_variation_derivative_ae R E N hN g hg he.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hVar)=> x [v [hv [hs _]]].
exists (N v)%:E; split.
- by exists v.
- exists (N v); split=> //; by rewrite (ger0_norm (real_seminorm_nonnegative hN.1 v)).
Qed.

(** Source for [normed_bv_norm_derivative_interval_integral]: direct
    finite norm-integral estimate extended by Federer 2.9.22,
    pp. 167–168, from 2.9.19, pp. 164–165. On every finite
    segment [a,b], the actual N(g') integral is nonnegative, finite
    and at most V_a^b g. The case a=b has zero integral and
    variation. Derivative existence almost everywhere is an explicit
    intermediate premise, proved for reflexive Banach curves above. *)
Theorem normed_bv_norm_derivative_interval_integral (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  forall a b : R, a<=b -> exists I : R, 0<=I /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (normed_curve_norm_derivative_integrand hN g) I%:E /\
    (I%:E<=curve_variation g a b)%E.
Proof.
move=> hg hExists a b hab.
have hs (u v : R) : u<=v -> arc_length g u<=arc_length g v :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg u v.
have hfin := @monotone_locally_finite_variation R (arc_length g) hs.
have [psip [psim hp]] := @induced_measure_pair_exists R (arc_length g) hfin.
have [I [hI0 [hi hb]]] := @real_bv_absolute_derivative_interval_integral R
  (arc_length g) psip psim a b hfin hp hab.
have he := @normed_bv_norm_arc_derivative_almost_equal R E N hN g hg hExists.
have heSubset := @zero_extension_almost_equal R (real_line_metric R) _
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) 0%E `[a,b] _ _
  (measure_almost_equal_sym he).
have hiN := @measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ I%:E hi heSubset.
rewrite (@monotone_curve_variation_eq R (arc_length g) hs a b hab)
  (@arc_length_increment R [the metricType R of real_norm_metric_space hN] g hg a b hab) in hb.
exists I; by split=> //; split.
Qed.
