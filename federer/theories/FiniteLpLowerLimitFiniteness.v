(** Federer (1969), 2.5.7, p. 98: bounded increasing sequences of candidate
    densities have almost finite limits. These supporting statements supply
    the actual power integrals from the sealed Lq norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower
  MeasureUP MeasureAlmostUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm MeasureLpPowerIntegral
  RealPower ExtendedPositivePower TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarLpNormLaws
  TotalExtendedLowerLimit TotalLowerLimitPowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_total_lp_power_integral]: the qth-power integral
    used in Federer 2.5.7, p. 98 This is the defining identity 2.4.12, p.
    86, for nonnegative total functions. *)
Lemma nonnegative_total_lp_power_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) (f : X -> R) :
  total_scalar_lp mu p%:E f -> (forall x, (0 <= f x)%R) ->
  is_measure_integral mu
    (partial_function_total (fun x => extended_positive_power (f x)%:E p))
    (real_power (finite_total_scalar_lp_norm mu p%:E f) p)%:E.
Proof.
move=> hf hf0.
have hp : (1 <= p)%R by move: hf.1; rewrite lee_fin.
have he : measure_lp_norm mu (fun y : R => `|y|%R) p (total_scalar_function f)=
    (finite_total_scalar_lp_norm mu p%:E f)%:E.
  exact: esym (@finite_total_scalar_lp_norm_exact R X mu hm p%:E f hf).
have hi := @measure_power_integral_from_finite_lp_norm R X R^o (fun y : R => `|y|%R)
  (scalar_absolute_value_norm R) mu hm p _ (total_scalar_function f) hp hf.2.1 he.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z; split.
- move=> [y [hy hz]]; have hy' : f x=y := hy.
  change ((real_power (f x) p)%:E=z).
  change ((real_power `|y| p)%:E=z) in hz.
  by rewrite -hy' (ger0_norm (hf0 x)) in hz.
- move=> hz; exists (f x); split=> //.
  by rewrite (ger0_norm (hf0 x)).
Qed.

(** Source for [finite_lp_bounded_lower_limit_almost_finite]: Fatou estimate
    excluding an infinite limit in Federer 2.5.7, p. 98 This strengthening
    needs only nonnegative terms and a uniform finite norm bound;
    monotonicity is unnecessary for finiteness. *)
Theorem finite_lp_bounded_lower_limit_almost_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p M : R) (f : nat -> X -> R) :
  (forall n, total_scalar_lp mu p%:E (f n)) ->
  (forall n x, (0 <= f n x)%R) ->
  (forall n, total_scalar_lp_norm mu p%:E (f n) <= M%:E) ->
  measure_almost_everywhere mu
    [set x | total_extended_lower_limit (fun n x => (f n x)%:E) x \is a fin_num].
Proof.
move=> hf hf0 hb.
have hp : (1 <= p)%R by move: (hf 0%N).1; rewrite lee_fin.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
apply: (@total_lower_limit_power_almost_finite R X mu hm _ p
  (fun n => real_power (finite_total_scalar_lp_norm mu p%:E (f n)) p) (real_power M p)).
- by move=> n x; rewrite lee_fin; exact: hf0.
- exact: hp0.
- move=> n; exact: (@nonnegative_total_lp_power_integral R X mu hm p (f n) (hf n) (hf0 n)).
- move=> n; apply: real_power_monotone=> //.
  + apply: fine_ge0; exact: (@total_scalar_lp_norm_nonnegative R X mu hm _ _ (hf n).1 (hf n).2.1).
  + have hh := hb n.
    by rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm p%:E (f n) (hf n)) lee_fin in hh.
Qed.
