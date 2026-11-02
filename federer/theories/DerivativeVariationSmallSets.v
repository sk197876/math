(** Federer (1969), 2.9.20, p. 166, application of 2.4.11: small
    Lebesgue-measurable subsets of a segment have small absolute derivative
    integrals. Finiteness is supplied by 2.9.19 before applying integral
    continuity. Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  RealBVDerivativeIntegral RealCurveDerivativeIntegrands DerivativeVariationMeasure
  NonnegativeSubsetIntegralContinuity MeasureIntegralUniqueness MeasureUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_derivative_variation_small_sets]: direct small-set
    integral estimate used for (2)=>(3) in Federer 2.9.20, p. 166 It holds
    for every locally finite-variation real curve, independently of equality
    (2), since 2.9.19 already gives a finite absolute derivative integral on
    [a,b]. No derivative measurability assumption is added. *)
Lemma real_derivative_variation_small_sets (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b e : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> (a<=b)%R -> (0<e)%R ->
  exists d : R, (0<d)%R /\ forall A : set (real_line_metric R),
    measure_measurable (@lebesgue_scalar_measure R) A -> A `<=` `[a,b] ->
    lebesgue_scalar_measure A<=d%:E -> real_derivative_variation_measure psip psim A<e%:E.
Proof.
move=> hg hp hab he.
have [I [hI0 [hI hbound]]] := @real_bv_absolute_derivative_interval_integral R g psip psim a b hg hp hab.
have [d [hd hsmall]] := @nonnegative_subset_integral_small_sets R (real_line_metric R)
  (@lebesgue_scalar_measure R) (real_curve_absolute_derivative_integrand g) `[a,b] I e
  (lebesgue_scalar_is_measure R) (@real_curve_absolute_derivative_nonnegative R g) hI he.
have [_ [hrep _]] := @real_derivative_variation_measure_laws R g psip psim hg hp.
exists d; split=> // A hA hAB hAd.
have [J [hJ hJe]] := hsmall A hA hAB hAd.
have hval := measure_integral_unique hJ (hrep A hA).2.
by rewrite -hval lte_fin.
Qed.
