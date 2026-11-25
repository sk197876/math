(** Federer (1969), 2.4.17, p. 90: lower estimates for norms as p tends to
    infinity. This supporting bound follows from the superlevel estimate of
    Federer 2.4.12, p. 87. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower ExtendedPositivePower
  ExtendedPowerProduct MeasureUP MeasurableFunctionUP MeasureGauge
  MeasureIntegralBounds MeasureNormPowerMarkov MeasureLpNorm MeasureLpNormFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_superlevel_root_bound]: Supporting Federer
    2.4.17, p. 90.The superlevel measure is a finite nonnegative m. *)
Lemma measure_lp_superlevel_root_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p r m : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (0 < r)%R -> (0 <= m)%R -> is_measure_measurable_function mu f ->
  mu (partial_norm_superlevel N f r%:E)=m%:E ->
  (r * real_power m p^-1)%:E <= measure_lp_norm mu N p f.
Proof.
move=> hp hr hm0 hf hmeasure.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
have hpi : (0 < p^-1)%R by rewrite invr_gt0.
have hb := @measure_norm_power_superlevel_bound R X V N hN mu hm p r f hp0 (ltW hr) hf.
rewrite hmeasure -EFinM in hb.
have hprod : 0 <= (real_power r p * m)%:E by rewrite lee_fin mulr_ge0 ?real_power_nonnegative.
have hh := @extended_positive_power_monotone R _ _ p^-1 hprod hb hpi.
rewrite -(@measure_lp_norm_lower_integral R X V N hN mu p f hm hp hf) in hh.
change (is_true ((real_power (real_power r p * m)%R p^-1)%:E <= measure_lp_norm mu N p f)) in hh.
rewrite real_power_product ?real_power_nonnegative // real_power_positive_iterate ?(ltW hr) //
  mulfV ?gt_eqF // real_power_one_exponent ?(ltW hr) // in hh.
Qed.
