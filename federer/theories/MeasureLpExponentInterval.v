(** Federer (1969), 2.4.17, p. 90: the finite-norm exponent set is an
    interval. The direct finite-endpoint estimate below uses domination by
    |f|^s+|f|^t, the same split at absolute value one used in its proof of
    (5). It is a supporting finite-endpoint case, not yet the assertion
    including the endpoint infinity or continuity on the closure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialExtendedArithmetic
  ExtendedRealPartial RealPower RealPowerExponentOrder MeasurableNormPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralAddition MeasureIntegralComparison
  MeasureNonnegativeIntegral MeasureLpNorm MeasureLpNormFiniteness MeasureLpPowerIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_finite_exponents_interval]: the
    finite-endpoint part of the interval assertion in Federer
    2.4.17, p. 90. Supporting generalization to arbitrary normed
    targets and the original partial domains is harmless here. *)
Lemma measure_lp_finite_exponents_interval (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (s p t : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= s)%R -> (s <= p)%R -> (p <= t)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N s f < +oo -> measure_lp_norm mu N t f < +oo ->
  measure_lp_norm mu N p f < +oo.
Proof.
move=> hs hsp hpt hf hsf htf.
have hp : (1 <= p)%R := le_trans hs hsp.
have ht : (1 <= t)%R := le_trans hp hpt.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have hp0 : (0 < p)%R := lt_le_trans hs0 hsp.
have hsn := @measure_lp_norm_nonnegative R X V N hN mu s f hm hs hf.
have htn := @measure_lp_norm_nonnegative R X V N hN mu t f hm ht hf.
have hsfin : measure_lp_norm mu N s f \is a fin_num by rewrite (ge0_fin_numE hsn).
have htfin : measure_lp_norm mu N t f \is a fin_num by rewrite (ge0_fin_numE htn).
pose a := fine (measure_lp_norm mu N s f).
pose b := fine (measure_lp_norm mu N t f).
have hsa : measure_lp_norm mu N s f=a%:E by rewrite /a fineK.
have htb : measure_lp_norm mu N t f=b%:E by rewrite /b fineK.
have hsi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm s a f hs hf hsa.
have hti := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm t b f ht hf htb.
have hadd : extended_add (real_power a s)%:E (real_power b t)%:E=
    Some ((real_power a s+real_power b t)%R)%:E by rewrite /extended_add /=.
have hsum := @measure_integral_add R X mu hm _ _ _ _ _ hsi hti hadd.
have hpm := @measurable_norm_positive_power R X V N hN mu hm p f hp0 hf.
have hpn := @partial_norm_power_almost_nonnegative R X _ mu hm N p f (measurable_function_domain hf).
have hi := (@nonnegative_measurable_function_integral R X mu hm _ hpm hpn).1.
have hbound : measure_lower_integral mu (partial_norm_power N p f) <= (real_power a s+real_power b t)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hi hsum).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
  move=> x [y hy]; exists (real_power (N y) p)%:E,(real_power (N y) s+real_power (N y) t)%:E; split.
  - exists y; by split.
  split.
  - apply/partial_extended_function_add_graph; exists (real_power (N y) s)%:E,(real_power (N y) t)%:E.
    split; first by exists y; split.
    split; first by exists y; split.
    by rewrite /extended_add /=.
  - rewrite lee_fin; exact: (@real_power_between_exponents_bound R (N y) s p t
      (real_seminorm_nonnegative hN.1 y) hs0 hsp hpt).
rewrite (@measure_lp_norm_finite_iff R X V N hN mu p f hm hp hf).
exact: le_lt_trans hbound (ltry _).
Qed.
