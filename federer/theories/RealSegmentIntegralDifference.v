(** Federer (1969), 2.9.20, proof p. 166: the difference of two finite
    indefinite integrals is the integral on the intervening segment.
    Endpoint singletons have zero scalar Lebesgue measure by 2.5.17, p. 111. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP MeasureUP MeasureSubsetIntegral LebesgueScalarMeasure
  NestedSubsetIntegralDifference SubsetIntegralNullReplacement
  RealCurveDerivativeIntegrands RealAbsoluteContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_segment_integral_finite_difference]: supporting
    finite interval additivity used in Federer 2.9.20, p. 166 Subtract on
    the nested closed segments, then restore the null left endpoint. The
    partial integrand need not be defined at any of the endpoints. *)
Lemma lebesgue_segment_integral_finite_difference (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (a u v A B : R) : a<=u -> u<=v ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,u] f A%:E ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,v] f B%:E ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] f (B-A)%:E.
Proof.
move=> hau huv hA hB; have hm := lebesgue_scalar_is_measure R.
have hsub : (`[a,u] : set (real_line_metric R)) `<=` `[a,v].
  move=> x; rewrite /= !in_itv /= => /andP[hax hxu].
  by rewrite hax (le_trans hxu huv).
have hI := @nested_subset_integral_finite_difference R (real_line_metric R)
  (@lebesgue_scalar_measure R) f `[a,u] `[a,v] A B hm hsub hA hB.
apply: (@subset_integral_null_replacement R (real_line_metric R)
  (@lebesgue_scalar_measure R) f (`[a,v] `\` `[a,u]) `[u,v] [set u] (B-A)%:E
  hm (lebesgue_scalar_singleton u) _ hI)=> x hxu.
split.
- move=> [hx hn]; move: hx; rewrite /= in_itv /= => /andP[hax hxv].
  have hux : u<x.
    rewrite ltNge; apply/negP=> hxu'; apply: hn.
    by rewrite /= in_itv /= hax hxu'.
  by rewrite /= in_itv /= (ltW hux) hxv.
- rewrite /= in_itv /= => /andP[hux hxv]; split.
  + by rewrite /= in_itv /= (le_trans hau hux) hxv.
  + rewrite /= in_itv /= => /andP[_ hxu']; apply: hxu.
    by apply/eqP; rewrite eq_le hux hxu'.
Qed.

(** Source for [indefinite_derivative_integral_subsegment]: supporting first
    observation in Federer 2.9.20, proof p. 166 Condition (1) yields the
    exact derivative integral over every closed subsegment, including a
    degenerate one; all integral values here are finite. *)
Lemma indefinite_derivative_integral_subsegment (R : realType) (g : R -> R)
    (a b u v : R) : real_curve_indefinite_derivative_integral g a b ->
  a<=u -> u<=v -> v<=b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v]
    (real_curve_derivative_integrand g) (g v-g u)%:E.
Proof.
move=> hg hau huv hvb.
have hu := hg u hau (le_trans huv hvb).
have hv := hg v (le_trans hau huv) hvb.
have hI := @lebesgue_segment_integral_finite_difference R
  (real_curve_derivative_integrand g) a u v (g u-g a) (g v-g a) hau huv hu hv.
have he : g v-g a-(g u-g a)=g v-g u by ring.
by rewrite he in hI.
Qed.
