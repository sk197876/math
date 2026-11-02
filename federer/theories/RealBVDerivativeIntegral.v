(** Federer (1969), 2.9.19, pp. 164–165: the integral of |g'| is bounded by
    total variation. Nonnegative extended integral sums retain their actual
    arithmetic domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength StieltjesImageMeasures
  StieltjesDerivationClass StieltjesContinuousPartBound RealCurveDerivativeIntegrands
  DerivativeIntegralAgreement ScalarIntervalDerivationContext DerivationIntegral
  MeasureDerivationContext MeasureUP MeasureBasic MeasureSubsetIntegral MeasureIntegralAddition
  MeasureIntegralAlmostEquality AbsoluteContinuousPart AbsoluteContinuousPartBasic
  PartialFunctionUP PartialZeroExtension PartialExtendedArithmetic ExtendedRealOrderTopology ExtendedRealPartial
  LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_bv_absolute_derivative_subset_integral_formula]:
    supporting integral identity in the last calculation of Federer 2.9.19,
    p. 165 By 2.9.7, each induced-measure derivate integrates to its
    continuous-part mass. The representation holds on every
    Lebesgue-measurable set, extending the interval case used by the book;
    positive-infinite values are retained where appropriate. *)
Theorem real_bv_absolute_derivative_subset_integral_formula (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (A : set (real_line_metric R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> measure_measurable (@lebesgue_scalar_measure R) A ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) A
    (real_curve_absolute_derivative_integrand g)
    ((@measure_continuous_part R [the topologicalType of real_line_metric R] psip
      (@lebesgue_scalar_measure R) A)+
     (@measure_continuous_part R [the topologicalType of real_line_metric R] psim
      (@lebesgue_scalar_measure R) A)).
Proof.
move=> hg hp hA.
have hm := lebesgue_scalar_is_measure R.
have [hCP hCM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
pose GP := @measure_continuous_part R [the topologicalType of real_line_metric R] psip (@lebesgue_scalar_measure R).
pose GM := @measure_continuous_part R [the topologicalType of real_line_metric R] psim (@lebesgue_scalar_measure R).
have hmGP := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R) hm (derivation_measure_law hCP).
have hmGM := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R) hm (derivation_measure_law hCM).
have hP0 : 0<=GP A := measure_nonnegative hmGP A.
have hM0 : 0<=GM A := measure_nonnegative hmGM A.
have hdef := ge0_adde_def hP0 hM0.
have hadd : extended_add (GP A) (GM A)=Some (GP A+GM A) by rewrite /extended_add hdef.
have hIP := (@federer_2_9_7 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psip (@scalar_nondegenerate_interval_relation R) A
  (scalar_interval_derivation_context R) hCP hA).2.
have hIM := (@federer_2_9_7 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psim (@scalar_nondegenerate_interval_relation R) A
  (scalar_interval_derivation_context R) hCM hA).2.
have hI := @measure_integral_add R (real_line_metric R) (@lebesgue_scalar_measure R) hm _ _
  (GP A) (GM A) (GP A+GM A) hIP hIM hadd.
have heq := @derivative_subset_sum_almost_equal R g psip psim A hg hp.
exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R) hm
  _ _ (GP A+GM A) hI heq).
Qed.

(** Source for [real_bv_absolute_derivative_interval_integral]: direct final
    estimate of Federer 2.9.19, pp. 164–165 The actual partial |g'| has a
    finite nonnegative integral on [a,b], bounded by V_a^b g.
    Continuous-part endpoint masses vanish even if g jumps there, so the
    open-interval measure bound proves the closed-interval integral
    estimate. The degenerate interval a=b is included as a boundary
    extension, with integral and variation both zero. *)
Theorem real_bv_absolute_derivative_interval_integral (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> (a<=b)%R -> exists I : R, (0<=I)%R /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (real_curve_absolute_derivative_integrand g) I%:E /\
    I%:E<=curve_variation (g : R -> real_line_metric R) a b.
Proof.
move=> hg hp hab; have hm := lebesgue_scalar_is_measure R.
have [hCP hCM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hA : measure_measurable (@lebesgue_scalar_measure R) `[a,b].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R) `[a,b]).
  exact: closed_borel_set (@segment_closed_real R a b).
pose GP := @measure_continuous_part R [the topologicalType of real_line_metric R] psip (@lebesgue_scalar_measure R).
pose GM := @measure_continuous_part R [the topologicalType of real_line_metric R] psim (@lebesgue_scalar_measure R).
pose J := GP `[a,b]+GM `[a,b].
have hI := @real_bv_absolute_derivative_subset_integral_formula R g psip psim `[a,b] hg hp hA.
have hb := @stieltjes_continuous_part_segment_bound R g psip psim a b hg hp hab.
have hmGP := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R) hm (derivation_measure_law hCP).
have hmGM := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R) hm (derivation_measure_law hCM).
have hJ0 : 0<=J := adde_ge0 (measure_nonnegative hmGP `[a,b]) (measure_nonnegative hmGM `[a,b]).
have hJfin : J \is a fin_num.
  rewrite (ge0_fin_numE hJ0); exact: le_lt_trans hb (@hg a b hab).
pose I := fine J.
have hJE : J=I%:E by rewrite /I fineK.
have hI0 : (0<=I)%R by move: hJ0; rewrite hJE lee_fin.
exists I; split; first exact hI0.
split; [by rewrite -hJE|by rewrite -hJE].
Qed.
