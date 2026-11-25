(** Federer (1969), 2.4.17, p. 90: continuity of the powered integral
    between finite-norm exponents. The proof here combines those regions
    into the summable bound |f|^s+|f|^t and applies Federer's 2.4.9
    directly. This proves the integral step; continuity of the varying root
    and closure endpoints is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower MeasurableNormPower
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureLpNorm MeasureNonnegativeIntegral MeasureBoundedConvergence MeasurePowerIntervalDominator
  MeasureExponentIntegralFatou ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_power_integral_sequence_continuity]: the
    finite-integral convergence step of Federer 2.4.17, p. 90 A summable
    bracket is explicit; no monotonicity of the exponent sequence is
    required. *)
Lemma measure_power_integral_sequence_continuity (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (s t q : R) (p : nat -> R) :
  (1 <= s)%R -> (s <= q)%R -> (q <= t)%R ->
  (forall n, (s <= p n)%R /\ (p n <= t)%R) ->
  is_measure_measurable_function mu f ->
  measure_lp_norm mu N s f < +oo -> measure_lp_norm mu N t f < +oo ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  extended_order_limit (fun n => measure_lower_integral mu (partial_norm_power N (p n) f))
    (measure_lower_integral mu (partial_norm_power N q f)).
Proof.
move=> hs hsq hqt hp hf hsf htf hl.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have hq : (0 < q)%R := lt_le_trans hs0 hsq.
have hpn n : (0 < p n)%R := lt_le_trans hs0 (hp n).1.
have [h [hh hb]] := @measure_power_interval_dominator R X V N hN mu hm s t f hs (le_trans hsq hqt) hf hsf htf.
have hfm n := @measurable_norm_positive_power R X V N hN mu hm (p n) f (hpn n) hf.
have hgm := @measurable_norm_positive_power R X V N hN mu hm q f hq hf.
have hlim : MeasureAlmostUP.measure_almost_everywhere mu (PartialDominatedConvergence.partial_extended_convergence_locus
    (fun n => partial_norm_power N (p n) f) (partial_norm_power N q f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
  exact: (@partial_norm_varying_power_convergence R X V N hN f p q hpn hq hl).
have [a [e [b [hai [hbi [hei [hel hal]]]]]]] := @measure_bounded_convergence R X mu hm _ _ h hh hfm hgm
  (fun n => hb (p n) (hp n).1 (hp n).2) hlim.
have ha n : measure_lower_integral mu (partial_norm_power N (p n) f)=(a n)%:E.
  exact: (@measure_lower_integral_unique R X mu _ _ _ (measure_lower_integral_specification mu _) (hai n).2.2).
have hb' : measure_lower_integral mu (partial_norm_power N q f)=b%:E.
  exact: (@measure_lower_integral_unique R X mu _ _ _ (measure_lower_integral_specification mu _) hbi.2.2).
have he : (fun n => measure_lower_integral mu (partial_norm_power N (p n) f))=(fun n => (a n)%:E).
  by apply/funext=> n; rewrite ha.
by rewrite he hb'.
Qed.
