(** Federer (1969), 2.4.12, p. 87: the quantitative bound of the
    convergence-in-measure gauge by the Lp norm. We follow the choice
    r^(p+1)=integral |f|^p. At integral zero, positive thresholds decreasing
    to zero avoid division by zero; at infinity the inequality is automatic. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  ExtendedPositivePower ExtendedPositivePowerOrder ExtendedPositivePowerIterate
  MeasureUP MeasurableFunctionUP MeasureIntegralBounds MeasureNonnegativeLowerIntegral
  MeasureGauge MeasureLpGaugeThreshold MeasureLpNorm MeasureLpNormFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_gauge_power_integral_bound]: supporting
    root expression in Federer 2.4.12, p. 87,
    with no summability premise. For an infinite powered-norm
    integral the bound is the extended-real endpoint inequality. *)
Lemma measure_gauge_power_integral_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> is_measure_measurable_function mu f ->
  measure_gauge mu N f <= extended_positive_power
    (measure_lower_integral mu (partial_norm_power N p f)) (p+1)^-1.
Proof.
move=> hp hf.
have hp1 : (0 < p+1)%R := addr_gt0 hp ltr01.
have hi : (0 < (p+1)^-1)%R by rewrite invr_gt0.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have hb0 := @measure_lower_integral_nonnegative R X mu hm _ hnonneg.
case hb: (measure_lower_integral mu (partial_norm_power N p f))=> [b| |] /=.
- have hbpos : (0 <= b)%R by move: hb0; rewrite hb lee_fin.
  pose r := real_power b (p+1)^-1.
  have hr0 : (0 <= r)%R := real_power_nonnegative b (p+1)^-1.
  have hroot : real_power r (p+1) = b.
    have h := @real_power_root_cancel R b (p+1)^-1 hbpos hi.
    by rewrite invrK in h.
  have [hrz|hrz] := eqVneq r 0%R.
  + have hbz : b = 0%R.
      by move: hroot; rewrite hrz real_power_zero_base ?gt_eqF // => <-.
    change (measure_gauge mu N f <= r%:E); rewrite hrz.
    apply/lee_addgt0Pr=> e he; rewrite add0e.
    apply: measure_gauge_bound.
    apply: (@measure_lp_gauge_positive_threshold R X V N hN mu hm p e f hp he hf).
    by rewrite hb hbz lee_fin real_power_nonnegative.
  + have hr : (0 < r)%R by rewrite lt_neqAle eq_sym hrz hr0.
    apply: measure_gauge_bound.
    apply: (@measure_lp_gauge_positive_threshold R X V N hN mu hm p r f hp hr hf).
    by rewrite hb hroot.
- exact: leey.
- by move: hb0; rewrite hb.
Qed.

(** Source for [measure_gauge_le_lp_norm_power]: direct quantitative
    comparison in Federer 2.4.12, p. 87 The printed Lp hypothesis can be
    weakened to measurability: infinite norm values give a valid
    extended-real bound as well. *)
Theorem measure_gauge_le_lp_norm_power (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  measure_gauge mu N f <= extended_positive_power (measure_lp_norm mu N p f) (p/(p+1))%R.
Proof.
move=> hp hf; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have hb0 := @measure_lower_integral_nonnegative R X mu hm _ hnonneg.
rewrite (@measure_lp_norm_lower_integral R X V N hN mu p f hm hp hf)
  (@extended_power_root_gauge_identity R _ p hb0 hp0).
exact (@measure_gauge_power_integral_bound R X V N hN mu hm p f hp0 hf).
Qed.
