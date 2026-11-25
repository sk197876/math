(** Federer (1969), 2.9.20, p. 166: (4) implies (1). First obtain the
    integral identity on strictly interior intervals from 2.9.2, 2.9.7 and
    2.9.19, then use relative continuity and 2.4.11 to approach the
    endpoints. Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  RealAbsoluteContinuityUP RealCurveDerivativeIntegrands RestrictedInducedDerivativeIntegral
  RealBVSignedDerivativeIntegral DerivativeVariationSmallSets SegmentIntegralEndpointExtension
  MeasureUP MeasureSubsetIntegral MeasureIntegralUniqueness LebesgueScalarMeasure
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_induced_integral_representation]: direct
    implication (4)=>(1) of Federer 2.9.20, p. 166 Use actual finite signed
    derivative integrals, their absolute bounds from 2.9.19, and 2.4.11 on
    the fixed ambient segment. Both omitted endpoint integrals tend to zero.
    Continuity is required only within [a,b]; no global continuity at a or b
    is silently imposed. *)
Theorem continuous_induced_integral_representation (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<b ->
  real_curve_continuous_induced_measures g psip psim a b ->
  real_curve_indefinite_derivative_integral g a b.
Proof.
move=> hg hp hab hConditions.
have [hc _] := hConditions.
have hL := lebesgue_scalar_is_measure R.
have hExists u v : a<=u -> u<=v -> v<=b -> exists I : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v]
      (real_curve_derivative_integrand g) I%:E.
  move=> hau huv hvb.
  have [I [hI _]] := @real_bv_signed_derivative_interval_integral R g psip psim u v hg hp huv.
  by exists I.
have hSmall e : 0<e -> exists d : R, 0<d /\ forall u v I : R,
    a<=u -> u<=v -> v<=b -> v-u<=d ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v]
      (real_curve_derivative_integrand g) I%:E -> `|I|<e.
  move=> he.
  have [d [hd hsmall]] := @real_derivative_variation_small_sets R g psip psim a b e
    hg hp (ltW hab) he.
  exists d; split=> // u v I hau huv hvb hwidth hI.
  have hMeas : measure_measurable (@lebesgue_scalar_measure R) `[u,v].
    apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
      (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
    exact: closed_borel_set (@segment_closed_real R u v).
  have hSub : (`[u,v] : set (real_line_metric R)) `<=` `[a,b].
    move=> x; rewrite /= !in_itv /= => /andP[hux hxv].
    by rewrite (le_trans hau hux) (le_trans hxv hvb).
  have hLen : (lebesgue_scalar_measure `[u,v]<=d%:E)%E.
    by rewrite lebesgue_scalar_segment // lee_fin.
  have hNu := hsmall `[u,v] hMeas hSub hLen.
  have [J [hJ [hvalue hJBound]]] := @real_bv_signed_derivative_interval_integral R g psip psim u v hg hp huv.
  have hJI : J=I by have := measure_integral_unique hJ hI; case.
  rewrite hJI in hJBound.
  have hfinal := le_lt_trans hJBound hNu.
  by move: hfinal; rewrite lte_fin.
have hInterior u v : a<u -> u<v -> v<b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v]
      (real_curve_derivative_integrand g) (g v-g u)%:E.
  exact: continuous_induced_derivative_integral_interior hg hp hConditions.
exact: segment_integral_identity_extend_endpoints hab hc hExists hSmall hInterior.
Qed.
