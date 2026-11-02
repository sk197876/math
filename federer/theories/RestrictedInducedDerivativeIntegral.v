(** Federer (1969), 2.9.20, p. 166, last proof paragraph: under condition
    (4), g(v)-g(u) is the derivative integral for a<u<v<b. The endpoints
    here are strictly interior, so relative continuity suffices for the
    2.5.17 increment law. Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  StieltjesDerivationClass MeasureDerivationContext StieltjesIntervalIncrements
  RealAbsoluteContinuityUP SegmentRelativeContinuity ContinuousPartRestrictedEquality
  RealBVSignedDerivativeIntegral RealCurveDerivativeIntegrands AbsoluteContinuousPart
  MeasureSubsetIntegral LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_induced_derivative_integral_interior]: direct
    interior-interval calculation in the proof of (4)=>(1), Federer 2.9.20,
    p. 166 On subsets of (a,b), restricted absolute continuity identifies
    each continuous-part mass with the induced measure itself. The finite
    signed derivative integral is their difference, which is the curve
    increment at its two continuity endpoints. *)
Lemma continuous_induced_derivative_integral_interior (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (a b u v : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  real_curve_continuous_induced_measures g psip psim a b ->
  (a<u)%R -> (u<v)%R -> (v<b)%R ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v]
    (real_curve_derivative_integrand g) (g v-g u)%:E.
Proof.
move=> hg hp [hc [hACp hACm]] hau huv hvb.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hsub : (`[u,v] : set (real_line_metric R)) `<=` `]a,b[.
  move=> x; rewrite /= !in_itv /= => /andP[hux hxv].
  by rewrite (lt_le_trans hau hux) (le_lt_trans hxv hvb).
have hEp := @restricted_absolute_continuous_part_value R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) psip `]a,b[ `[u,v] (lebesgue_scalar_is_measure R)
  (derivation_measure_law hP) (derivation_measure_borel_regular hP) hACp hsub.
have hEm := @restricted_absolute_continuous_part_value R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) psim `]a,b[ `[u,v] (lebesgue_scalar_is_measure R)
  (derivation_measure_law hM) (derivation_measure_borel_regular hM) hACm hsub.
have hcu := @segment_continuity_interior R g a b u hc hau (lt_trans huv hvb).
have hcv := @segment_continuity_interior R g a b v hc (lt_trans hau huv) hvb.
have hincr := @stieltjes_induced_pair_closed_interval_increment R g psip psim u v
  hg hp huv hcu hcv.
have [I [hI [hval hbound]]] := @real_bv_signed_derivative_interval_integral R g psip psim u v
  hg hp (ltW huv).
rewrite hEp hEm -hincr in hval.
by rewrite hval in hI.
Qed.
