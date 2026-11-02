(** Federer (1969), 2.4.17, p. 90: finite positive superlevel measures in
    the infinity-endpoint argument. The supporting proof uses Federer's
    superlevel estimate in 2.4.12, p. 87. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower MeasureUP MeasureBasic
  MeasurableFunctionUP MeasureGauge MeasureIntegralBounds MeasureNormPowerMarkov MeasureLpNorm MeasureLpNormFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_lp_positive_superlevel_finite]: Supporting Federer
    2.4.17, p. 90. *)
Lemma finite_lp_positive_superlevel_finite (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p r : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (0 < r)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p f < +oo -> mu (partial_norm_superlevel N f r%:E) < +oo.
Proof.
move=> hp hr hf hfin.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
have hi : measure_lower_integral mu (PartialNormPower.partial_norm_power N p f) < +oo.
  by rewrite -(@measure_lp_norm_finite_iff R X V N hN mu p f hm hp hf).
have hb := @measure_norm_power_superlevel_bound R X V N hN mu hm p r f hp0 (ltW hr) hf.
have hc : 0 < (real_power r p)%:E by rewrite lte_fin; exact: real_power_strictly_positive hr.
have [hh|hh] := ltP (mu (partial_norm_superlevel N f r%:E)) +oo; first by [].
have he : mu (partial_norm_superlevel N f r%:E)=+oo by apply/eqP; rewrite eq_le leey hh.
rewrite he gt0_muley // in hb.
have hbad := le_lt_trans hb hi; by move: hbad; rewrite ltxx.
Qed.
