(** Federer (1969), 2.4.14, p. 88: the cases where one finite-p norm
    vanishes in Holder's inequality. The norm definition is Federer 2.4.12,
    p. 86. These supporting results allow an arbitrary normed target and
    preserve partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialNormPower RealPower MeasurableNormPower MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral
  MeasureNonnegativeLowerIntegral MeasureLpNorm MeasureLpNormFiniteness
  ExtendedPositivePower ExtendedPositivePowerOrder MeasureNonnegativeZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_lp_norm_power_integral]: supporting
    zero-norm case in Federer 2.4.14, p. 88:
    a zero norm forces the integral of its positive power
    to vanish, including the p=1 boundary. *)
Lemma zero_lp_norm_power_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f -> measure_lp_norm mu N p f = 0 ->
  is_measure_integral mu (partial_norm_power N p f) 0.
Proof.
move=> hp hf hz; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have hmeas := @measurable_norm_positive_power R X V N hN mu hm p f hp0 hf.
have hi := (@nonnegative_measurable_function_integral R X mu hm _ hmeas hnonneg).1.
have hb0 := @measure_lower_integral_nonnegative R X mu hm _ hnonneg.
rewrite (@measure_lp_norm_lower_integral R X V N hN mu p f hm hp hf) in hz.
have he := congr1 (fun x => extended_positive_power x p) hz.
rewrite extended_positive_power_inverse_cancel // extended_positive_power_zero // in he.
by rewrite he in hi.
Qed.

(** Source for [zero_lp_norm_almost_zero]: supporting assertion needed
    before normalisation in Federer 2.4.14, p. 88 A measurable function with
    zero finite-p norm vanishes almost everywhere. *)
Lemma zero_lp_norm_almost_zero (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f -> measure_lp_norm mu N p f = 0 ->
  measure_almost_equal mu f
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN))).
Proof.
move=> hp hf hz; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hi := @zero_lp_norm_power_integral R X V N hN mu hm p f hp hf hz.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have he := @nonnegative_integral_zero_almost_equal R X mu hm _ hi hnonneg.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [z [[y [hy hpow]] hz0]].
have hzero : (real_power (N y) p)%:E = 0 by rewrite hpow -(hz0 : 0=z).
have hn0 : N y=0%R.
  have [hne|hne] := eqVneq (N y) 0%R; first exact hne.
  have hnpos : (0 < N y)%R.
    by rewrite lt_neqAle eq_sym hne (real_seminorm_nonnegative hN.1).
  have hpos := @real_power_strictly_positive R (N y) p hnpos.
  have hposE : (0 : \bar R) < (real_power (N y) p)%:E by rewrite lte_fin.
  by move: hposE; rewrite hzero ltxx.
have hy0 := hN.2 y hn0.
exists y; split=> //; by rewrite hy0.
Qed.

(** Source for [lp_norm_zero_iff]: complete supporting zero-norm equivalence
    for the degenerate cases of Federer 2.4.14, p. 88 The function is
    measurable and the exponent finite and at least one; countable
    measurability is not an additional premise. *)
Lemma lp_norm_zero_iff (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  (measure_lp_norm mu N p f = 0 <-> measure_almost_equal mu f
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)))).
Proof.
move=> hp hf; split; first exact (@zero_lp_norm_almost_zero R X V N hN mu hm p f hp hf).
move=> he; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have hepow : measure_almost_equal mu (partial_norm_power N p f)
    (partial_function_total (fun _ : X => (0 : extended_real_line R))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [y [hy hy0]]; exists 0; split=> //; exists y; split=> //.
  have hy0' : (0%R : V)=y := hy0.
  by rewrite -hy0' (real_seminorm_zero hN.1) real_power_zero_base ?gt_eqF.
have hi := (@nonnegative_integral_zero_iff R X mu hm _ hnonneg).2 hepow.
rewrite (@measure_lp_norm_of_integral R X V N hN mu p f 0 hm hp hf hi).
apply: extended_positive_power_zero; by rewrite invr_gt0.
Qed.
