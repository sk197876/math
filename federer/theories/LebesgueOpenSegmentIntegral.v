(** Supporting omission of endpoints in Federer (1969), 2.6.3(2), pp.
    117–118. Singletons have zero L^1 measure by 2.5.17, p. 111; changing
    the restricted integrand there preserves its integral by 2.4.3(2), p.
    81, and the subset convention in 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  SummableRealFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_closed_open_segment_integral]: supporting
    equality of open- and closed-interval integrals in Federer
    2.6.3(2), pp. 117–118, from the zero
    endpoint masses in 2.5.17, p. 111. No
    continuity assumption on the integrand is needed. *)
Lemma lebesgue_closed_open_segment_integral (R : realType) (f : R -> R) (a b : R) (z : \bar R) :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b] (real_total_integrand f) z ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `]a,b[ (real_total_integrand f) z.
Proof.
move=> hi; have hm := lebesgue_scalar_is_measure R.
apply: (measure_integral_almost_equal hm hi).
have hN : lebesgue_scalar_measure ([set a] `|` [set b])=0%E.
  exact (@measure_null_union R R _ hm [set a] [set b] (@lebesgue_scalar_singleton R a) (@lebesgue_scalar_singleton R b)).
have hcon : measure_almost_everywhere (@lebesgue_scalar_measure R) (~` ([set a] `|` [set b])).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_almost_everywhere_mono R R _ hm _ _ _ hcon)=> x hx.
have hxa : x != a by apply/eqP=> he; apply: hx; left; exact: he.
have hxb : x != b by apply/eqP=> he; apply: hx; right; exact: he.
case: (pselect (`[a,b] x))=> hclosed.
- have hopen : `]a,b[ x.
    move: hclosed; rewrite /= !in_itv /= => /andP[hax hxb'];
    by rewrite !lt_neqAle eq_sym hxa hxb hax hxb'.
  exists (f x)%:E; split.
  + by apply/(partial_function_zero_extension_on _ _ _ hclosed); exact/real_total_integrand_graph.
  + by apply/(partial_function_zero_extension_on _ _ _ hopen); exact/real_total_integrand_graph.
- have hopen : ~ `]a,b[ x.
    move=> hh; apply: hclosed; move: hh; rewrite /= !in_itv /= => /andP[hax hxb'];
    by rewrite (ltW hax) (ltW hxb').
  exists 0%E; split.
  + by apply/(partial_function_zero_extension_off _ _ _ hclosed).
  + by apply/(partial_function_zero_extension_off _ _ _ hopen).
Qed.
