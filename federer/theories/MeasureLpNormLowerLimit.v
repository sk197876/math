(** Federer (1969), 2.4.12, p. 87: finite-p lower semicontinuity from
    Fatou's lemma. The proof follows the printed argument through powered
    norms and positive roots. Exact partial domains and infinite norm values
    are retained; completeness of the target is unnecessary for this
    inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP PartialDominatedConvergence
  PartialNormPower PartialNormPowerLimit MeasurableNormPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral MeasureNonnegativeLowerIntegral
  MeasureFatouConvergent ExtendedLowerLimitUP ExtendedLowerLimit
  ExtendedPositivePower ExtendedPositivePowerLowerLimit MeasureLpNorm MeasureLpNormFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_norm_lower_semicontinuous]: direct finite-p
    lower-limit inequality in Federer 2.4.12, p. 87 The limit is assumed
    measurable, as required to specify its Lp value; the project's
    measurable-limit theorem separately supplies that premise for
    almost-everywhere limits in A. *)
Theorem measure_lp_norm_lower_semicontinuous (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R ->
  (forall n, is_measure_measurable_function mu (f n)) ->
  is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  measure_lp_norm mu N p g <= extended_lower_limit (fun n => measure_lp_norm mu N p (f n)).
Proof.
move=> hp hf hg hl.
have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hi : (0 < p^-1)%R by rewrite invr_gt0.
pose u n := measure_lower_integral mu (partial_norm_power N p (f n)).
pose b := measure_lower_integral mu (partial_norm_power N p g).
have hfp n := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p (f n) (measurable_function_domain (hf n)).
have hgp := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p g (measurable_function_domain hg).
have hu n : is_measure_integral mu (partial_norm_power N p (f n)) (u n).
  exact (@nonnegative_measurable_function_integral R X mu hm _
    (@measurable_norm_positive_power R X V N hN mu hm p (f n) hp0 (hf n)) (hfp n)).1.
have hb : is_measure_integral mu (partial_norm_power N p g) b.
  exact (@nonnegative_measurable_function_integral R X mu hm _
    (@measurable_norm_positive_power R X V N hN mu hm p g hp0 hg) hgp).1.
have hlim : measure_almost_everywhere mu
    (partial_extended_convergence_locus (fun n => partial_norm_power N p (f n))
      (partial_norm_power N p g)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl).
  exact (@partial_norm_power_convergence_locus R X V N hN p f g hp0).
have hfatou := @measure_fatou_convergent_values R X mu hm _ _ u b hlim hfp hu hb.
have hu0 n : 0 <= u n := @measure_lower_integral_nonnegative R X mu hm _ (hfp n).
have hb0 : 0 <= b := @measure_lower_integral_nonnegative R X mu hm _ hgp.
have hroot := @extended_positive_power_monotone R b (extended_lower_limit u) p^-1 hb0 hfatou hi.
have hlroot := @extended_positive_power_lower_limit R u (extended_lower_limit u) p^-1
  hu0 hi (extended_lower_limit_laws u).
have he := extended_lower_limit_unique hlroot
  (extended_lower_limit_laws (fun n => extended_positive_power (u n) p^-1)).
have hen : (fun n => measure_lp_norm mu N p (f n)) =
    (fun n => extended_positive_power (u n) p^-1).
  apply: funext=> n; exact (@measure_lp_norm_lower_integral R X V N hN mu p (f n) hm hp (hf n)).
rewrite hen (@measure_lp_norm_lower_integral R X V N hN mu p g hm hp hg).
by rewrite -he.
Qed.
