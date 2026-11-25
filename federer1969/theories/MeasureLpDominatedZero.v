(** Federer (1969), 2.4.12, p. 87: finite-image density uses bounded
    convergence from 2.4.9, p. 85, on powered approximation errors. This
    supporting lemma isolates the powered-integral convergence step while
    keeping arbitrary partial domains and a supplied majorant. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP PartialNormPower PartialNormPowerLimit PartialExtendedArithmetic PartialExtendedOrderLoci
  PartialDominatedConvergence PartialAbsolutePartsGraph RealPower MeasurableNormPower MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  MeasureDensityNullSets MeasureNonnegativeLowerIntegral MeasureIntegralBounds MeasureBoundedConvergence
  MeasureLpNorm MeasureLpIntegralLimit ExtendedRealOrderLimit ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_power_dominated_zero_limit]: supporting finite-p
    bounded-convergence consequence for Federer 2.4.12, p. 87
    Almost-everywhere convergence of vectors to zero, together with a
    summable majorant for their powered norms, implies finite norms and
    convergence of those norms to zero. No completeness hypothesis is needed
    once the limit is given. *)
Theorem lp_power_dominated_zero_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (h : partial_function X (extended_real_line R)) :
  (1 <= p)%R -> (forall n, is_measure_measurable_function mu (f n)) ->
  is_measure_summable mu h ->
  (forall n, measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_norm_power N p (f n))) h)) ->
  measure_almost_everywhere mu (partial_function_limit_locus f
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)))) ->
  (forall n, measure_lp_norm mu N p (f n) < +oo) /\
    extended_order_limit (fun n => measure_lp_norm mu N p (f n)) 0.
Proof.
move=> hp hf hh hb hl.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
pose z := partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)).
pose zp := partial_norm_power N p z.
have hzi : is_measure_integral mu zp 0.
  apply: (@measure_integral_graph_equivalent R X mu _ zp 0 _ (measure_extended_zero_integral hm))=> x t; split.
  - move=> ht; exists 0%R; split=> //.
    have ht' : (0 : \bar R)=t := ht.
    by rewrite (real_seminorm_zero hN.1) real_power_zero_base ?gt_eqF // ht'.
  - move=> [u [hu hut]]; have hu' : (0%R : V)=u := hu.
    change ((0 : \bar R)=t).
    by rewrite -hu' (real_seminorm_zero hN.1) real_power_zero_base ?gt_eqF // in hut.
have hpm n := @measurable_norm_positive_power R X V N hN mu hm p (f n) hp0 (hf n).
have hpl : measure_almost_everywhere mu
    (partial_extended_convergence_locus (fun n => partial_norm_power N p (f n)) zp).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl).
  exact (@partial_norm_power_convergence_locus R X V N hN p f z hp0).
have [a [e [b [hai [hbi [hei [hel hal]]]]]]] := @measure_bounded_convergence R X mu hm
  (fun n => partial_norm_power N p (f n)) zp h hh hpm hzi.1 hb hpl.
have hb0 : b%:E=0 := measure_integral_unique hbi hzi.
rewrite hb0 in hal.
have ha0 n : 0 <= (a n)%:E.
  have hn := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
    mu hm N p (f n) (measurable_function_domain (hf n)).
  have hnon := @measure_lower_integral_nonnegative R X mu hm _ hn.
  have heq := measure_lower_integral_unique (hai n).2.2 (measure_lower_integral_specification mu _).
  by rewrite heq.
split.
- move=> n; rewrite (@measure_lp_norm_of_integral R X V N hN mu p (f n) (a n)%:E hm hp (hf n) (hai n)).
  change ((real_power (a n) p^-1)%:E < +oo); exact: ltry.
- exact (@lp_norm_zero_limit_of_power_integrals R X V N hN mu hm p f (fun n => (a n)%:E) hp hf ha0 hai hal).
Qed.
