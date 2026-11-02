(** Federer (1969), 2.4.14, p. 88: recover the powered-norm integrals of the
    normalised functions from their Lp norms. The defining formula is
    Federer 2.4.12, p. 86. These are supporting root-cancellation
    consequences of the public norm specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower MeasurableNormPower
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral
  MeasureNonnegativeLowerIntegral MeasureLpNorm MeasureLpNormFiniteness
  ExtendedPositivePower ExtendedPositivePowerOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_power_integral_from_finite_lp_norm]:
    supporting identification of the normalising denominator in
    Federer 2.4.14, p. 88. The norm may be zero;
    only finiteness of its specified real value is required. *)
Lemma measure_power_integral_from_finite_lp_norm (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f -> measure_lp_norm mu N p f = a%:E ->
  is_measure_integral mu (partial_norm_power N p f) (real_power a p)%:E.
Proof.
move=> hp hf ha; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have hmeas := @measurable_norm_positive_power R X V N hN mu hm p f hp0 hf.
have hi := (@nonnegative_measurable_function_integral R X mu hm _ hmeas hnonneg).1.
have hb0 := @measure_lower_integral_nonnegative R X mu hm _ hnonneg.
rewrite (@measure_lp_norm_lower_integral R X V N hN mu p f hm hp hf) in ha.
have he := congr1 (fun x => extended_positive_power x p) ha.
rewrite extended_positive_power_inverse_cancel // in he.
change (measure_lower_integral mu (partial_norm_power N p f)=(real_power a p)%:E) in he.
by rewrite he in hi.
Qed.

(** Source for [measure_power_integral_normalised]: the unit integral of the
    normalised power in Federer 2.4.14, p. 88 *)
Lemma measure_power_integral_normalised (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f -> measure_lp_norm mu N p f = 1 ->
  is_measure_integral mu (partial_norm_power N p f) 1.
Proof.
move=> hp hf ha.
have h := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p 1%R f hp hf ha.
by rewrite real_power_one_base in h.
Qed.
