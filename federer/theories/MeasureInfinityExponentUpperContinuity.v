(** Federer (1969), 2.4.17, p. 90: upper continuity at infinity when the
    essential norm is positive finite. The proof below uses the explicit
    chord and its scalar limit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureLpNorm MeasureEssentialNorm MeasureInfinityInterpolationChord
  RealPowerInterpolationLimit PositiveReciprocalOrderLimit RealScalarOrderLimits ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_infinity_exponent_eventual_upper_bound]: Supporting
    Federer 2.4.17, p. 90.One positive finite Ls norm supplies the chord. *)
Lemma measure_infinity_exponent_eventual_upper_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (s A B : R) (p : nat -> R) :
  (1 <= s)%R -> (forall n, (1 <= p n)%R) -> (0 < A)%R -> (0 < B)%R ->
  is_measure_measurable_function mu f -> measure_essential_norm mu N f=A%:E ->
  measure_lp_norm mu N s f=B%:E -> extended_order_limit (fun n => (p n)%:E) +oo ->
  forall b, A%:E < b -> exists k, forall n, (k <= n)%N -> measure_lp_norm mu N (p n) f < b.
Proof.
move=> hs hp hA hB hf hea hsb hl b hb.
have hp0 n : (0 < p n)%R := lt_le_trans ltr01 (hp n).
have hrec := @positive_reciprocal_infinity_order_limit R p hp0 hl.
have hsrec := @real_scalar_order_limit R (fun n => ((p n)^-1)%R) 0%R s hrec.
rewrite mulr0 in hsrec.
have hchord := @real_power_interpolation_endpoint_limit R (fun n => (s/p n)%R) A B hA hB hsrec.
have [j hj] := hchord.2 b hb; have [k hk] := hl.1 s%:E (ltry s).
exists (maxn j k)=> n hn; apply: le_lt_trans _ (hj n (leq_trans (leq_maxl j k) hn)).
exact: (@measure_infinity_interpolation_chord R X V N hN mu hm s (p n) A B f hs
  (hk n (leq_trans (leq_maxr j k) hn)) hA hf hea hsb).
Qed.
