(** Supporting exponent limit for Federer (1969), 2.10.9, p. 175, using the
    probability norm assertion of 2.4.17, p. 90. Finite-exponent Fatou lower
    bounds and the infinity superlevel lower bound combine with probability
    monotonicity. A finite first norm suffices; the limiting norm may be
    infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasureExponentDomain MeasureLpNorm MeasureLpExponentLowerContinuity
  MeasureInfinityExponentLowerContinuity ProbabilityExponentMonotone
  ExtendedRealOrderLimit ExtendedOrderLimitShift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_scalar_norm_left_sequence_limit]:
    supporting norm limit for the left-exponent limit in Federer
    2.10.9, p. 175, from 2.4.17, p. 90. Real exponents stay
    between one and the limiting extended exponent. They need
    not increase or be strictly below it. Only the norm at one
    is required finite, including when the target exponent is infinity. *)
Theorem probability_scalar_norm_left_sequence_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (g : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (p : nat -> R) (t : \bar R) :
  mu setT = 1 -> (forall n, (1<=p n)%R /\ (p n)%:E<=t) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_exponent_norm mu (partial_function_total g) 1< +oo ->
  extended_order_limit (fun n => (p n)%:E) t ->
  extended_order_limit (fun n => measure_exponent_norm mu (partial_function_total g) (p n)%:E)
    (measure_exponent_norm mu (partial_function_total g) t).
Proof.
move=> hprob hp hg hfin hlim.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
split.
- move=> a ha.
  have hp1 n := (hp n).1.
  clear hp.
  case: t ht hlim ha=> [q| |] ht hlim ha; last by move: ht; rewrite leNgt ltNyr.
  + exact: (@measure_lp_exponent_eventual_lower_bound R X R^o
      (fun y : R => `|y|%R) (scalar_absolute_value_norm R) mu hm
      (partial_function_total g) q p ht hp1 hg hlim a ha).
  + pose v n := if n is k.+1 then p k else 1%R.
    have hv n : (1<=v n)%R by case: n=> [|n] //=; exact: hp1 n.
    have hvlim : extended_order_limit (fun n => (v n)%:E) +oo.
      apply: (@extended_order_limit_of_shift R (fun n => (v n)%:E) +oo 1).
      have he : (fun n => (v (1+n)%N)%:E)=(fun n => (p n)%:E).
        apply: funext=> n; by rewrite add1n.
      by rewrite he.
    have hvfin : measure_lp_norm mu (fun y : R => `|y|%R) (v 0%N)
      (partial_function_total g)< +oo := hfin.
    have [N hN] := @measure_infinity_exponent_eventual_lower_bound R X R^o
      (fun y : R => `|y|%R) (scalar_absolute_value_norm R) mu hm
      (partial_function_total g) v hv hg hvfin hvlim a ha.
    exists N=> n hn.
    have hh := hN n.+1 (leq_trans hn (leqnSn n)); exact hh.
- move=> b hb; exists 0%N=> n _.
  apply: le_lt_trans _ hb.
  exact: (@probability_measure_exponent_norm_monotone R X mu hm (partial_function_total g)
    (p n)%:E t hprob (hp n).1 (hp n).2 hg).
Qed.
