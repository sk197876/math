(** Federer (1969), 2.4.12, pp. 86–87: the norm superlevel estimate and
    redundancy of countable measurability for finite p. The proofs use
    characteristic lower functions and the project's own integral laws; no
    external Markov or Lp theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasureUP MeasurableFunctionUP MeasurableNormSuperlevels MeasureGauge MeasureIntegralBounds
  MeasureNormPowerMarkov MeasureLpNorm MeasureLpNormFiniteness ExtendedRealReciprocalBounds
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [norm_nonzero_locus_reciprocal_superlevels]: supporting
    countable cover for the parenthetical assertion in Federer 2.4.12, p. 86
    Exact partial domains are retained. *)
Lemma norm_nonzero_locus_reciprocal_superlevels (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) (f : partial_function X V) :
  partial_function_nonzero_locus (0%R : V) f =
    \bigcup_n partial_norm_superlevel N f (((n.+1)%:R : R)^-1)%:E.
Proof.
apply/seteqP; split=> x.
- move=> [y [hy hy0]]; have hypos : (0 < N y)%R.
    rewrite (real_norm_positive hN.1 hN.2); exact/eqP.
  have [n hn] := positive_reciprocal_nat_small hypos; exists n=> //.
  exists y; split=> //; by rewrite lte_fin.
- move=> [n _ [y [hy hny]]]; exists y; split=> // => he.
  have hny' : (((n.+1)%:R : R)^-1 < N y)%R := hny.
  move: hny'; by rewrite he (real_seminorm_zero hN.1) ltNge invr_ge0 ler0n.
Qed.

(** Source for [finite_lp_norm_countably_measurable]: complete parenthetical
    assertion that countable measurability is redundant for finite p in
    Federer 2.4.12, p. 86 *)
Theorem finite_lp_norm_countably_measurable (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p f < +oo ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space hN) f.
Proof.
move=> hp hf hfin; constructor=> //.
apply/(countably_measurable_sequence_iff hm).
exists (fun n => partial_norm_superlevel N f (((n.+1)%:R : R)^-1)%:E); split.
- exact (@norm_nonzero_locus_reciprocal_superlevels R X V N hN f).
- move=> n; split; first exact (@measurable_norm_superlevel R X V N hN mu hm f hf _).
  have hr : (0 < ((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
  have hb := @measure_norm_power_superlevel_bound R X V N hN mu hm p _ f hp0 (ltW hr) hf.
  have hi : measure_lower_integral mu (partial_norm_power N p f) < +oo.
    by rewrite -(@measure_lp_norm_finite_iff R X V N hN mu p f hm hp hf).
  have hprod := le_lt_trans hb hi.
  case he: (mu (partial_norm_superlevel N f (((n.+1)%:R : R)^-1)%:E))=> [a| |]; rewrite ?ltry ?ltNyy //.
  move: hprod; rewrite he gt0_muley ?ltxx // lte_fin.
  exact: real_power_strictly_positive hr.
Qed.
