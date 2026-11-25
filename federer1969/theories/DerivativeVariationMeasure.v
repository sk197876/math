(** Federer (1969), 2.9.20, pp. 165–166: regard the integral of |g'| over a
    variable set as the sum of the two continuous parts, as proved at the
    end of 2.9.19, p. 165. This public adapter uses only sealed continuous
    parts and their proved laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  StieltjesImageMeasures StieltjesDerivationClass MeasureDerivationContext ScalarIntervalDerivationContext
  LebesgueScalarMeasure MeasureUP MeasureBinaryAddition AbsoluteContinuousPart
  ContinuousPartMeasurableSets StieltjesContinuousPartBound RealCurveDerivativeIntegrands
  RealBVDerivativeIntegral MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_derivative_variation_measure]: supporting measure in
    Federer 2.9.20, p. 166, given by the exact continuous-part integral
    formula at the end of 2.9.19, p. 165 It is defined by the sum of the two
    abstract public operators, without selecting representing densities or
    assigning derivative values outside their actual domain. *)
Definition real_derivative_variation_measure (R : realType)
    (psip psim : set R -> \bar R) (A : set R) :=
  @measure_continuous_part R [the topologicalType of real_line_metric R]
    psip (@lebesgue_scalar_measure R) A+
  @measure_continuous_part R [the topologicalType of real_line_metric R]
    psim (@lebesgue_scalar_measure R) A.

(** Source for [real_derivative_variation_measure_laws]: supporting measure
    laws for the proof of Federer 2.9.20, p. 166, using 2.9.19, p. 165 The
    measure represents the actual |g'| integral on every Lebesgue-measurable
    set, preserves those measurable sets, has no atoms, and is dominated on
    each closed segment by variation even at jump endpoints. *)
Theorem real_derivative_variation_measure_laws (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  let nu := real_derivative_variation_measure psip psim in
  is_measure nu /\
  (forall A, measure_measurable (@lebesgue_scalar_measure R) A ->
    measure_measurable nu A /\ is_measure_subset_integral (@lebesgue_scalar_measure R)
      A (real_curve_absolute_derivative_integrand g) (nu A)) /\
  (forall x : R, nu [set x]=0) /\
  (forall a b : R, (a<=b)%R -> nu `[a,b]<=curve_variation (g : R -> real_line_metric R) a b).
Proof.
move=> hg hp nu; have hL := lebesgue_scalar_is_measure R.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hP; have hmM := derivation_measure_law hM.
pose GP := @measure_continuous_part R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R).
pose GM := @measure_continuous_part R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R).
have hGP := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R) hL hmP.
have hGM := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R) hL hmM.
split; first exact: measure_binary_addition_is_measure hGP hGM.
split.
- move=> A hA; split.
  + apply: measure_binary_addition_measurable.
    * exact (@continuous_part_preserves_measurable_sets R [the metricType R of real_line_metric R]
        (@lebesgue_scalar_measure R) psip
        (derivation_context_measure (scalar_interval_derivation_context R)) hP A hA).
    * exact (@continuous_part_preserves_measurable_sets R [the metricType R of real_line_metric R]
        (@lebesgue_scalar_measure R) psim
        (derivation_context_measure (scalar_interval_derivation_context R)) hM A hA).
  + exact: real_bv_absolute_derivative_subset_integral_formula hg hp hA.
split.
- move=> x; change (GP [set x]+GM [set x]=0).
  by rewrite /GP /GM (@scalar_continuous_part_singleton_null R psip x hmP)
    (@scalar_continuous_part_singleton_null R psim x hmM) add0e.
- move=> a b hab; exact: stieltjes_continuous_part_segment_bound hg hp hab.
Qed.
