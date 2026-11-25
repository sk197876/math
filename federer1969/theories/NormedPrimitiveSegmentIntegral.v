(** Federer (1969), 2.9.22, pp. 167–168: vector-integral step in the
    extension of 2.9.20(1)=>(2), p. 166. Subtract the two finite indefinite
    integrals through each continuous dual functional. The actual subsegment
    integral follows from its abstract specification and the independently
    proved full L1 membership; no computation through an integral
    construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP CurveArcLength
  NormedCurveDerivativeUP NormedCurveAbsoluteContinuityUP BVDerivativeLocalIntegrability
  MeasureVectorIntegralUP ContinuousRealFunctional MeasureIntegralUP MeasureUP
  MeasureRestriction MeasureSubsetIntegral RestrictedIntegralIdentity RealSegmentIntegralDifference
  LebesgueScalarMeasure RealMetricBackground MeasureAlmostUP
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_indefinite_derivative_integral_subsegment]:
    direct supporting subsegment identity for Federer 2.9.22,
    pp. 167–168, extending the first step of 2.9.20(1)=>(2),
    p. 166. Subtract the finite scalar evaluations on [a,u]
    and [a,v], restore the null endpoint, and use the vector integral
    specification. The actual derivative may be absent at endpoints;
    both u=v and repeated source endpoints are included. *)
Theorem normed_indefinite_derivative_integral_subsegment (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN)
    (a b u v : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists w : E, has_normed_curve_derivative N g x w] ->
  normed_curve_indefinite_derivative_integral hN g a b -> a<=u -> u<=v -> v<=b ->
  @is_measure_vector_integral R (real_line_metric R) E N hN
    (measure_restrict (@lebesgue_scalar_measure R) (`[u,v] : set (real_line_metric R)))
    (normed_curve_derivative hN g) (g v-g u).
Proof.
move=> hY hg he hF hau huv hvb.
have hL := lebesgue_scalar_is_measure R.
have hclosed p q : measure_measurable (@lebesgue_scalar_measure R) `[p,q].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R p q).
have hU := hF u hau (le_trans huv hvb).
have hV := hF v (le_trans hau huv) hvb.
split; first exact (@normed_bv_derivative_interval_lone R E N hN g hY hg he u v huv).
move=> f hf.
have hIU := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL `[a,u] _ _ (hclosed a u)).1 (hU.2 f hf).
have hIV := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL `[a,v] _ _ (hclosed a v)).1 (hV.2 f hf).
have hDiff := @lebesgue_segment_integral_finite_difference R
  (partial_functional_evaluation (normed_curve_derivative hN g) f) a u v
  (f (g u-g a)) (f (g v-g a)) hau huv hIU hIV.
have hVal : f (g v-g a)-f (g u-g a)=f (g v-g u).
  by rewrite -linearB opprB addrA subrK.
rewrite hVal in hDiff.
exact ((@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL `[u,v] _ _ (hclosed u v)).2 hDiff).
Qed.
