(** Federer (1969), 2.4.15, first proof paragraph p. 89: f+g belongs to Lp
    before the Minkowski estimate is applied. The resulting closure also
    supports the Lebesgue-space discussion in Federer 2.4.12, pp. 86–87. All
    partial-domain membership conditions are retained; total functions are
    needed only for the literal vector-space assertions in the erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  ExtendedPositivePower MeasureNormSumPower MeasureLpPowerIntegral MeasureLpNorm MeasureLpMembershipUP
  MeasurableNormedArithmetic MeasureLpCountableMeasurability MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_function_add]: direct preliminary Lp closure in
    Federer 2.4.15, p. 89 The same proof includes p=1 and arbitrary normed
    targets, beyond the printed p>1 Banach-space application. *)
Theorem measure_lp_function_add (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  is_measure_lp_function mu p (partial_vector_add f g).
Proof.
move=> hf hg; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hf.1.
have hfnn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hf.1 hf.2.1.1.
have hgnn := @measure_lp_norm_nonnegative R X V N hN mu p g hm hg.1 hg.2.1.1.
have hffin : measure_lp_norm mu N p f \is a fin_num.
  rewrite (ge0_fin_numE hfnn); exact hf.2.2.1.
have hgfin : measure_lp_norm mu N p g \is a fin_num.
  rewrite (ge0_fin_numE hgnn); exact hg.2.2.1.
pose a := fine (measure_lp_norm mu N p f).
pose b := fine (measure_lp_norm mu N p g).
have hfa : measure_lp_norm mu N p f = a%:E by rewrite fineK.
have hgb : measure_lp_norm mu N p g = b%:E by rewrite fineK.
have hfi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p a f hf.1 hf.2.1.1 hfa.
have hgi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p b g hg.1 hg.2.1.1 hgb.
have [c [hc [hci hbound]]] := @measure_norm_sum_power_finite_integral R X V N hN mu hm p _ _ f g
  hp0 hf.2.1 hg.2.1 hfi hgi.
have hfg := @measurable_normed_function_add R X V N hN mu hm f g hf.2.1 hg.2.1.
have hfin : measure_lp_norm mu N p (partial_vector_add f g) < +oo.
  by rewrite (@measure_lp_norm_of_integral R X V N hN mu p _ c%:E hm hf.1 hfg.1 hci)
    /extended_positive_power ltry.
split; first exact hf.1.
split=> //; split=> //.
exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p _ hf.1 hfg.1 hfin).
Qed.
