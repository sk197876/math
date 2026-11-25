(** Federer (1969), 2.4.12, pp. 86-87: passing from convergence of
    powered-norm integrals to Lp convergence, supporting finite-image
    density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower MeasureUP
  MeasurableFunctionUP MeasureIntegralUP MeasureLpNorm ExtendedRealOrderLimit
  ExtendedPositivePower ExtendedPositivePowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_norm_zero_limit_of_power_integrals]: supporting
    root-continuity step for finite-image density in Federer 2.4.12,
    p. 87. The integral values are supplied by their abstract laws;
    no construction of the integral or of the norm is unfolded. *)
Lemma lp_norm_zero_limit_of_power_integrals (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN)) (a : nat -> \bar R) :
  (1 <= p)%R -> (forall n, is_measure_measurable_function mu (f n)) ->
  (forall n, 0 <= a n) -> (forall n, is_measure_integral mu (partial_norm_power N p (f n)) (a n)) ->
  extended_order_limit a 0 -> extended_order_limit (fun n => measure_lp_norm mu N p (f n)) 0.
Proof.
move=> hp hf ha hi hl.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
have hip : (0 < p^-1)%R by rewrite invr_gt0.
have hh := @extended_positive_power_order_limit R a 0 p^-1 ha (lexx 0) hip hl.
rewrite extended_positive_power_zero // in hh.
have he : (fun n => measure_lp_norm mu N p (f n)) =
    (fun n => extended_positive_power (a n) p^-1).
  apply: funext=> n; exact (@measure_lp_norm_of_integral R X V N hN mu p (f n) (a n) hm hp (hf n) (hi n)).
by rewrite he.
Qed.
