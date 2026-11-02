(** Federer (1969), 2.4.16, p. 89: at p=1, integral |f| equals phi_1(f),
    including zero and infinity. This uses the norm definition in 2.4.12, p.
    86. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  MeasureUP MeasurableFunctionUP MeasurableNormPower MeasureIntegralUP MeasureIntegralBounds
  MeasureNonnegativeIntegral MeasureNonnegativeLowerIntegral MeasureLpNorm MeasureLpNormFiniteness ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_lone_norm_integral]: supporting
    integral |f|=phi_1(f) in Federer 2.4.16, p. 89. Unlike
    the L1 membership formulation, this includes infinite norm. *)
Lemma measurable_lone_norm_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function mu f ->
  is_measure_integral mu (partial_norm_power N 1%R f) (measure_lp_norm mu N 1%R f).
Proof.
move=> hf.
have hpos := @partial_norm_power_almost_nonnegative R X _ mu hm N 1%R f
  (measurable_function_domain hf).
have hmeas := @measurable_norm_positive_power R X V N hN mu hm 1%R f ltr01 hf.
have hi := (@nonnegative_measurable_function_integral R X mu hm _ hmeas hpos).1.
have hn := @measure_lower_integral_nonnegative R X mu hm _ hpos.
have he := @measure_lp_norm_of_integral R X V N hN mu 1%R f _ hm (lexx _) hf hi.
rewrite invr1 extended_positive_power_one // in he.
by rewrite he.
Qed.
