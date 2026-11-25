(** Federer (1969), 2.4.12, p. 87: positive superlevel bounds and the
    finite-image step in vector integration. Each nonzero fibre of an L1
    finite-image function has finite measure. The supporting results below
    hold for every finite p> = 1 and do not require finite image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasureUP MeasureBasic MeasureGauge MeasureNormPowerMarkov MeasureLpNormFiniteness
  MeasureIntegralBounds MeasureLpMembershipUP MeasurableFunctionUP MeasurableFunctionBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_positive_superlevel_finite]: supporting
    consequence of the displayed superlevel inequality in Federer 2.4.12, p.
    87 *)
Lemma measure_lp_positive_superlevel_finite (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p r : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f -> (0 < r)%R -> mu (partial_norm_superlevel N f r%:E) < +oo.
Proof.
move=> hf hr; have hp0 : (0 < p)%R := lt_le_trans ltr01 hf.1.
have hb := @measure_norm_power_superlevel_bound R X V N hN mu hm p r f hp0 (ltW hr) hf.2.1.1.
have hfinite : measure_lower_integral mu (partial_norm_power N p f) < +oo.
  rewrite -(@measure_lp_norm_finite_iff R X V N hN mu p f hm hf.1 hf.2.1.1); exact hf.2.2.1.
have hprod := le_lt_trans hb hfinite.
case he: (mu (partial_norm_superlevel N f r%:E))=> [a| |]; rewrite ?ltry ?ltNyy //.
move: hprod; rewrite he gt0_muley ?ltxx // lte_fin.
exact: real_power_strictly_positive hr.
Qed.

(** Source for [measure_lp_nonzero_fibre_finite]: supporting finite fibre
    measures for the elementary-function argument in Federer 2.4.12, pp.
    87–88 The zero fibre is excluded, since it may have infinite measure. *)
Lemma measure_lp_nonzero_fibre_finite (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) (y : V) :
  is_measure_lp_function mu p f -> y != 0%R ->
  measure_measurable mu (partial_function_preimage f [set y]) /\
  mu (partial_function_preimage f [set y]) < +oo.
Proof.
move=> hf hy; split.
- apply: (@measurable_function_borel_preimage R X [the topologicalType of real_norm_metric_space hN]
    mu hm f hf.2.1.1).
  apply: closed_borel_set; apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
- have hny : (0 < N y)%R by rewrite (real_norm_positive hN.1 hN.2).
  have hr : (0 < N y/2)%R by rewrite divr_gt0 // ltr0n.
  have hsmall : (N y/2 < N y)%R by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
  apply: le_lt_trans (@measure_mono R X mu hm _ (partial_norm_superlevel N f (N y/2)%:E) _) _.
  + move=> x [z [hz he]]; exists z; split=> //; change (is_true (N y/2 < N z)%R); by rewrite (he : z=y).
  + exact (@measure_lp_positive_superlevel_finite R X V N hN mu hm p (N y/2)%R f hf hr).
Qed.
