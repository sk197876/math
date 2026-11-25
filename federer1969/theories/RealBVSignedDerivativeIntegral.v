(** Federer (1969), 2.9.20, p. 166: integrate g' as the difference of the
    two finite induced-measure derivates on a bounded interval. Finiteness
    is proved before subtraction, and the actual partial derivative is
    retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  StieltjesImageMeasures StieltjesDerivationClass MeasureDerivationContext
  AbsoluteContinuousPart DerivativeVariationMeasure DerivativeDifferenceAgreement
  RealCurveDerivativeIntegrands ScalarIntervalDerivationContext DerivationIntegral
  MeasureUP MeasureSubsetIntegral MeasureIntegralDifference MeasureIntegralAlmostEquality
  MeasureIntegralAbsolute MeasureIntegralUniqueness DerivativeAbsoluteIntegralBound
  LebesgueScalarMeasure TopologicalBorel BorelRegularMeasureUP IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_bv_signed_derivative_interval_integral]: supporting
    signed integral identity for Federer 2.9.20, p. 166 On each closed
    segment, g' has a finite integral equal to the difference of the two
    continuous-part masses, and its absolute value is bounded by their sum.
    This existence assertion holds even when g is not absolutely continuous;
    no endpoint continuity is used. *)
Theorem real_bv_signed_derivative_interval_integral (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> (a<=b)%R -> exists I : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (real_curve_derivative_integrand g) I%:E /\
    I%:E=(@measure_continuous_part R [the topologicalType of real_line_metric R]
      psip (@lebesgue_scalar_measure R) `[a,b]-
      @measure_continuous_part R [the topologicalType of real_line_metric R]
      psim (@lebesgue_scalar_measure R) `[a,b]) /\
    `|I|%:E<=real_derivative_variation_measure psip psim `[a,b].
Proof.
move=> hg hp hab; have hL := lebesgue_scalar_is_measure R.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
pose GP := @measure_continuous_part R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R).
pose GM := @measure_continuous_part R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R).
have hmGP := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R) hL (derivation_measure_law hP).
have hmGM := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R) hL (derivation_measure_law hM).
have [hmNu [hrep [hz hbound]]] := @real_derivative_variation_measure_laws R g psip psim hg hp.
have hA : measure_measurable (@lebesgue_scalar_measure R) `[a,b].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R a b).
have hGP0 := measure_nonnegative hmGP `[a,b].
have hGM0 := measure_nonnegative hmGM `[a,b].
have hNuFin : real_derivative_variation_measure psip psim `[a,b]< +oo.
  exact: le_lt_trans (hbound a b hab) (hg a b hab).
have hGPFin : GP `[a,b] \is a fin_num.
  rewrite (ge0_fin_numE hGP0); apply: le_lt_trans _ hNuFin.
  exact: lee_paddr hGM0 (lexx _).
have hGMFin : GM `[a,b] \is a fin_num.
  rewrite (ge0_fin_numE hGM0); apply: le_lt_trans _ hNuFin.
  exact: lee_paddl hGP0 (lexx _).
pose P := fine (GP `[a,b]); pose M := fine (GM `[a,b]).
have hPE : GP `[a,b] = P%:E by rewrite /P fineK.
have hME : GM `[a,b] = M%:E by rewrite /M fineK.
have hIP := (@federer_2_9_7 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psip (@scalar_nondegenerate_interval_relation R) `[a,b]
  (scalar_interval_derivation_context R) hP hA).2.
have hIM := (@federer_2_9_7 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psim (@scalar_nondegenerate_interval_relation R) `[a,b]
  (scalar_interval_derivation_context R) hM hA).2.
rewrite -/GP hPE in hIP; rewrite -/GM hME in hIM.
have hDiff := @measure_integral_finite_difference R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL _ _ P M hIP hIM.
have hI := @measure_integral_almost_equal R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL _ _ (P-M)%:E hDiff
  (@derivative_subset_difference_almost_equal R g psip psim `[a,b] hg hp).
exists (P-M)%R; split; first exact hI.
split.
- change ((P-M)%:E=GP `[a,b]-GM `[a,b]); by rewrite hPE hME -EFinB.
- have [J [hJ hIJ]] := @derivative_subset_integral_absolute_bound R g
    (@lebesgue_scalar_measure R) `[a,b] (P-M)%R hL hI.
  have hval := measure_integral_unique hJ (hrep `[a,b] hA).2.
  by rewrite hval in hIJ.
Qed.
