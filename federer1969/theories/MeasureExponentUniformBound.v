(** Federer (1969), 2.4.17, p. 90: lower control at a limiting finite
    exponent, including infinite norm values. This supporting closed-bound
    statement uses Fatou and continuity of a fixed scalar base raised to the
    varying exponent. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  RealPower RealPowerExponentLimit ExtendedPositivePower ExtendedPositivePowerOrder
  MeasureUP MeasurableFunctionUP MeasureIntegralBounds MeasureNonnegativeLowerIntegral
  MeasureLpNorm MeasureLpNormFiniteness MeasureExponentIntegralFatou
  ExtendedRealOrderLimit ExtendedConvergentLowerLimit ExtendedLowerLimitUP ExtendedLowerLimit
  ExtendedLowerLimitMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_exponent_uniform_bound_closed]: supporting
    passage of a uniform norm bound to a finite exponent limit in Federer
    2.4.17, p. 90 This bound supplies lower semicontinuity without assuming
    that the limiting norm is finite. *)
Lemma measure_lp_exponent_uniform_bound_closed (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (q a : R) (p : nat -> R) :
  (1 <= q)%R -> (forall n, (1 <= p n)%R) -> (0 <= a)%R ->
  is_measure_measurable_function mu f ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  (forall n, measure_lp_norm mu N (p n) f <= a%:E) -> measure_lp_norm mu N q f <= a%:E.
Proof.
move=> hq hp ha hf hl hb.
have hq0 : (0 < q)%R := lt_le_trans ltr01 hq.
have hp0 n : (0 < p n)%R := lt_le_trans ltr01 (hp n).
have hfn n := @partial_norm_power_almost_nonnegative R X _ mu hm N (p n) f (measurable_function_domain hf).
have hgn := @partial_norm_power_almost_nonnegative R X _ mu hm N q f (measurable_function_domain hf).
have hn n := @measure_lower_integral_nonnegative R X mu hm _ (hfn n).
have hg := @measure_lower_integral_nonnegative R X mu hm _ hgn.
have hbound n : measure_lower_integral mu (partial_norm_power N (p n) f) <= (real_power a (p n))%:E.
  have hh := @extended_positive_power_monotone R (measure_lp_norm mu N (p n) f) a%:E (p n)
    (@measure_lp_norm_nonnegative R X V N hN mu (p n) f hm (hp n) hf) (hb n) (hp0 n).
  by rewrite (@measure_lp_norm_lower_integral R X V N hN mu (p n) f hm (hp n) hf)
    extended_positive_power_inverse_cancel // in hh.
have hfatou := @measure_exponent_integral_fatou R X V N hN mu hm f p q hf hp0 hq0 hl.
have hmono := @extended_lower_limit_pointwise_monotone R _ _ hbound.
have hlim := @real_power_exponent_order_limit R p q a ha hq0 hp0 hl.
have he := @extended_lower_limit_unique R _ _ _ (extended_lower_limit_laws _)
  (@extended_convergent_lower_limit R _ _ hlim).
have hi : measure_lower_integral mu (partial_norm_power N q f) <= (real_power a q)%:E.
  by rewrite -he; exact: le_trans hfatou hmono.
have hqi : (0 < q^-1)%R by rewrite invr_gt0.
have hh := @extended_positive_power_monotone R _ _ q^-1 hg hi hqi.
rewrite -(@measure_lp_norm_lower_integral R X V N hN mu q f hm hq hf) in hh.
change (is_true (measure_lp_norm mu N q f <= (real_power (real_power a q) q^-1)%:E)) in hh.
by rewrite real_power_positive_iterate // mulfV ?gt_eqF // real_power_one_exponent // in hh.
Qed.
