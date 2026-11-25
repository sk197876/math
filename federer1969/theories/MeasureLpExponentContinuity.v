(** Federer (1969), 2.4.17, p. 90: continuity in a finite exponent bracket.
    This supporting sequence theorem follows those two steps. The bracket
    endpoints have finite norms; continuity on the whole closure, including
    infinite-norm endpoints and the infinity exponent, is a separate
    assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  MeasureUP MeasurableFunctionUP MeasureIntegralBounds MeasureNonnegativeLowerIntegral
  MeasureLpNorm MeasureLpNormFiniteness MeasureExponentIntegralContinuity
  ExtendedRealOrderLimit ExtendedVaryingPowerLimit PositiveReciprocalOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_exponent_bracket_continuity]: the
    summable-bracket case of the continuity assertion in Federer 2.4.17, p.
    90 Generalization to partial normed-valued functions uses exactly the
    same scalar powered integrands. *)
Theorem measure_lp_exponent_bracket_continuity (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (s t q : R) (p : nat -> R) :
  (1 <= s)%R -> (s <= q)%R -> (q <= t)%R ->
  (forall n, (s <= p n)%R /\ (p n <= t)%R) ->
  is_measure_measurable_function mu f ->
  measure_lp_norm mu N s f < +oo -> measure_lp_norm mu N t f < +oo ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  extended_order_limit (fun n => measure_lp_norm mu N (p n) f) (measure_lp_norm mu N q f).
Proof.
move=> hs hsq hqt hp hf hsf htf hl.
have hq1 : (1 <= q)%R := le_trans hs hsq.
have hq : (0 < q)%R := lt_le_trans ltr01 hq1.
have hp1 n : (1 <= p n)%R := le_trans hs (hp n).1.
have hp0 n : (0 < p n)%R := lt_le_trans ltr01 (hp1 n).
have hp' n : (0 < (p n)^-1)%R by rewrite invr_gt0.
have hq' : (0 < q^-1)%R by rewrite invr_gt0.
have hlim := @measure_power_integral_sequence_continuity R X V N hN mu hm f s t q p hs hsq hqt hp hf hsf htf hl.
have hroot := @positive_reciprocal_order_limit R p q hp0 hq hl.
have hfn n := @partial_norm_power_almost_nonnegative R X _ mu hm N (p n) f (measurable_function_domain hf).
have hgn := @partial_norm_power_almost_nonnegative R X _ mu hm N q f (measurable_function_domain hf).
have hu n := @measure_lower_integral_nonnegative R X mu hm _ (hfn n).
have hg := @measure_lower_integral_nonnegative R X mu hm _ hgn.
have hh := @extended_varying_power_order_limit R _ _ _ q^-1 hu hg hp' hq' hlim hroot.
have he : (fun n => measure_lp_norm mu N (p n) f)=
    (fun n => ExtendedPositivePower.extended_positive_power (measure_lower_integral mu (partial_norm_power N (p n) f)) (p n)^-1).
  apply/funext=> n; exact: (@measure_lp_norm_lower_integral R X V N hN mu (p n) f hm (hp1 n) hf).
by rewrite he (@measure_lp_norm_lower_integral R X V N hN mu q f hm hq1 hf).
Qed.
