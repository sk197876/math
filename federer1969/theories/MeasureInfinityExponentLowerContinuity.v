(** Federer (1969), 2.4.17, p. 90: lower continuity at the infinity
    exponent. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower MeasureUP MeasureBasic
  MeasurableFunctionUP MeasureGauge MeasureLpNorm MeasureEssentialNorm
  MeasureLpSuperlevelRoot MeasureFiniteLpSuperlevel
  ExtendedRealOrderTopology ExtendedRealOrderLimit RealScalarOrderLimits
  PositiveReciprocalOrderLimit RealPowerExponentLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_infinity_exponent_eventual_lower_bound]: Supporting
    Federer 2.4.17, p. 90.One finite input norm suffices for the superlevel
    measure argument. *)
Theorem measure_infinity_exponent_eventual_lower_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (p : nat -> R) :
  (forall n, (1 <= p n)%R) -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N (p 0%N) f < +oo ->
  extended_order_limit (fun n => (p n)%:E) +oo -> forall a,
  a < measure_essential_norm mu N f ->
  exists k, forall n, (k <= n)%N -> a < measure_lp_norm mu N (p n) f.
Proof.
move=> hp hf hfin hl a ha.
have hp0 n : (0 < p n)%R := lt_le_trans ltr01 (hp n).
have [ha0|ha0] := leP 0 a; last first.
- exists 0%N=> n hn; apply: lt_le_trans ha0 _.
  exact: (@measure_lp_norm_nonnegative R X V N hN mu (p n) f hm (hp n) hf).
have [r [har hre]] := @extended_rationals_order_dense R a (measure_essential_norm mu N f) ha.
have hr0e : 0 < (ratr r : R)%:E := le_lt_trans ha0 har.
have hr0 : (0 < ratr r :> R)%R := hr0e.
pose A := partial_norm_superlevel N f (ratr r : R)%:E.
have hA0 := measure_nonnegative hm A.
have hApos : 0 < mu A.
  rewrite lt_neqAle eq_sym hA0 andbT; apply/eqP=> hz.
  have he : measure_essential_norm mu N f <= (ratr r : R)%:E.
    apply: measure_essential_norm_bound; split=> //; exact: ltW hr0e.
  by move: hre; rewrite ltNge he.
have hAfin := @finite_lp_positive_superlevel_finite R X V N hN mu hm (p 0%N) (ratr r : R) f (hp 0%N) hr0 hf hfin.
have hAnum : mu A \is a fin_num by rewrite (ge0_fin_numE hA0).
pose m := fine (mu A).
have hAm : mu A=m%:E by rewrite /m fineK.
have hmpos : (0 < m)%R by move: hApos; rewrite hAm lte_fin.
have hrec := @positive_reciprocal_infinity_order_limit R p hp0 hl.
have hpow := @real_power_positive_base_exponent_limit R (fun n => ((p n)^-1)%R) 0%R m hmpos hrec.
rewrite real_power_zero_exponent in hpow.
have hscaled := @real_scalar_order_limit R (fun n => real_power m (p n)^-1) 1%R (ratr r : R) hpow.
rewrite mulr1 in hscaled.
have [k hk] := hscaled.1 a har; exists k=> n hn.
apply: lt_le_trans (hk n hn) _.
exact: (@measure_lp_superlevel_root_bound R X V N hN mu hm (p n) (ratr r : R) m f
  (hp n) hr0 (ltW hmpos) hf hAm).
Qed.
