(** Federer (1969), 2.4.17, p. 90: probability-space norm monotonicity with
    upper exponent infinity. Here the endpoint proof is written as
    comparison with the constant essential bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower
  RealPower ExtendedPositivePower MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormPower
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison MeasureNonnegativeIntegral
  MeasureNonnegativeLowerIntegral MeasureLpNorm MeasureLpNormFiniteness
  MeasureEssentialNorm MeasureEssentialNormAttainment ProbabilityConstantIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_infinity_lp_monotone_bound]: endpoint case of
    the last assertion of Federer 2.4.17, p. 90 The bound is finite and may
    vanish; the normed target is arbitrary. *)
Lemma probability_infinity_lp_monotone_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (s a : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  mu setT= 1 -> (1 <= s)%R -> is_measure_measurable_function mu f ->
  measure_essential_norm mu N f=a%:E -> measure_lp_norm mu N s f <= a%:E.
Proof.
move=> hprob hs hf hea.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have hsi : (0 < s^-1)%R by rewrite invr_gt0.
have hsne : s != 0%R by rewrite gt_eqF.
have ha0 : (0 <= a)%R.
  have hh := measure_essential_norm_nonnegative mu N f.
  by move: hh; rewrite hea lee_fin.
have hfm := @measurable_norm_positive_power R X V N hN mu hm s f hs0 hf.
have hfn := @partial_norm_power_almost_nonnegative R X _ mu hm N s f (measurable_function_domain hf).
have hfi := (@nonnegative_measurable_function_integral R X mu hm _ hfm hfn).1.
have hci := @probability_constant_integral R X mu hm (real_power a s) hprob.
have hbound : measure_lower_integral mu (partial_norm_power N s f) <= (real_power a s)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hfi hci).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_essential_norm_almost_bound R X _ mu hm N f (measurable_function_domain hf))).
  move=> x [y [hy hya]].
  have hyr : (N y <= a)%R by move: hya; rewrite hea lee_fin.
  exists (real_power (N y) s)%:E,(real_power a s)%:E; split; first by exists y; split.
  split=> //; rewrite lee_fin.
  exact: (@real_power_monotone R (N y) a s (real_seminorm_nonnegative hN.1 y) hyr hs0).
have hh := @extended_positive_power_monotone R _ _ s^-1
  (@measure_lower_integral_nonnegative R X mu hm _ hfn) hbound hsi.
rewrite -(@measure_lp_norm_lower_integral R X V N hN mu s f hm hs hf) in hh.
change (is_true (measure_lp_norm mu N s f <= (real_power (real_power a s) s^-1)%:E)) in hh.
by rewrite real_power_positive_iterate // mulfV // real_power_one_exponent // in hh.
Qed.
