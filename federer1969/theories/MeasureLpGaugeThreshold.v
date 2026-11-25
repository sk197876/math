(** Federer (1969), 2.4.12, p. 87: derive a gauge bound from the estimate
    r^p mu{|f|>r} <= integral |f|^p. This is the supporting
    positive-threshold step; the full root formula is stated separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  RealPower RealPowerSuccessor MeasureUP MeasurableFunctionUP MeasureIntegralBounds
  MeasureGauge MeasureNormPowerMarkov.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_gauge_positive_threshold]: supporting
    implication in Federer 2.4.12, p. 87: whenever
    r>0 and the powered-norm integral is at most r^(p+1),
    r is feasible in the gauge definition. No finite ambient
    measure or finite-dimensional target is assumed. *)
Lemma measure_lp_gauge_positive_threshold (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p r : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> (0 < r)%R -> is_measure_measurable_function mu f ->
  measure_lower_integral mu (partial_norm_power N p f) <= (real_power r (p+1))%:E ->
  measure_gauge_feasible mu N f r%:E.
Proof.
move=> hp hr hf hb; split; first by rewrite lee_fin; exact: ltW hr.
have hmarkov := @measure_norm_power_superlevel_bound R X V N hN mu hm p r f hp (ltW hr) hf.
have hprod := le_trans hmarkov hb.
rewrite (@real_power_positive_successor R r p (ltW hr) hp) EFinM in hprod.
move: hprod; rewrite lee_pmul2l ?fin_numE ?lte_fin //.
exact: real_power_strictly_positive hr.
Qed.
