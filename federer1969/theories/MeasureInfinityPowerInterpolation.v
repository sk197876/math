(** Federer (1969), 2.4.17, p. 90: Holder interpolation with one infinity
    endpoint. The supporting bound |f|^(r+s)<=a^r|f|^s uses the attained
    essential bound a; this is the endpoint Holder estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower RealPowerSuccessor
  MeasurableNormPower MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison MeasureIntegralScaleLaw MeasureUpperIntegralScale
  MeasureNonnegativeIntegral MeasureNonnegativeLowerIntegral MeasureLpNorm MeasureLpNormFiniteness MeasureLpPowerIntegral ExtendedPositivePower
  MeasureEssentialNorm MeasureEssentialNormAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_infinity_power_interpolation]: Supporting Federer
    2.4.17, p. 90.The finite essential norm is positive; a zero essential
    norm is handled by almost equality. *)
Lemma measure_infinity_power_interpolation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (r s a b : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (0 < r)%R -> (1 <= s)%R -> (0 < a)%R ->
  is_measure_measurable_function mu f ->
  measure_essential_norm mu N f=a%:E -> measure_lp_norm mu N s f=b%:E ->
  measure_lp_norm mu N (r+s)%R f <=
    (real_power (real_power a r * real_power b s)%R (r+s)^-1)%:E.
Proof.
move=> hr hs ha hf hea hsb.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have hp0 : (0 < r+s)%R by rewrite addr_gt0.
have hsp : (s <= r+s)%R by rewrite lerDr ltW.
have hp : (1 <= r+s)%R := le_trans hs hsp.
pose c := real_power a r.
have hc : (0 < c)%R := @real_power_strictly_positive R a r ha.
have hsi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm s b f hs hf hsb.
have hscale := @measure_integral_positive_scale R X mu hm c _ _ hc hsi.
rewrite -EFinM in hscale.
have hpm := @measurable_norm_positive_power R X V N hN mu hm (r+s)%R f hp0 hf.
have hpn := @partial_norm_power_almost_nonnegative R X _ mu hm N (r+s)%R f (measurable_function_domain hf).
have hpi := (@nonnegative_measurable_function_integral R X mu hm _ hpm hpn).1.
have hbound : measure_lower_integral mu (partial_norm_power N (r+s)%R f) <= (c * real_power b s)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hpi hscale).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_essential_norm_almost_bound R X _ mu hm N f (measurable_function_domain hf))).
  move=> x [y [hy hya]].
  have hyaR : (N y <= a)%R by move: hya; rewrite hea lee_fin.
  exists (real_power (N y) (r+s)%R)%:E,(c * real_power (N y) s)%:E; split.
  - exists y; by split.
  split.
  - exists (real_power (N y) s)%:E; split; last exact: EFinM.
    exists y; by split.
  - rewrite lee_fin.
    have [hy0|hy0] := eqVneq (N y) 0%R.
    + by rewrite hy0 !real_power_zero_base ?gt_eqF // mulr0.
    have hyn : (0 < N y)%R by rewrite lt_neqAle eq_sym hy0 (real_seminorm_nonnegative hN.1 y).
    rewrite (@real_power_add_exponents_positive R (N y) r s hyn).
    have hpow := @real_power_monotone R (N y) a r (real_seminorm_nonnegative hN.1 y) hyaR hr.
    exact: (ler_wpM2r (real_power_nonnegative (N y) s) hpow).
rewrite (@measure_lp_norm_lower_integral R X V N hN mu (r+s)%R f hm hp hf).
apply: (@extended_positive_power_monotone R _ _ (r+s)^-1 _ hbound _).
- exact: (@measure_lower_integral_nonnegative R X mu hm _ hpn).
- by rewrite invr_gt0.
Qed.
