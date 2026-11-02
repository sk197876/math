(** Federer (1969), 2.4.17, p. 90: lower continuity at finite exponents,
    including infinite limiting norms. This supporting consequence of Fatou
    turns the closed uniform-bound property into eventual lower bounds. The
    selected cofinal indices are local witnesses in the contradiction proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureLpNorm MeasureExponentUniformBound ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_exponent_eventual_lower_bound]: supporting lower
    half of continuity in Federer 2.4.17, p. 90 No finite-norm hypothesis is
    imposed on the sequence or the limit. *)
Theorem measure_lp_exponent_eventual_lower_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (q : R) (p : nat -> R) :
  (1 <= q)%R -> (forall n, (1 <= p n)%R) -> is_measure_measurable_function mu f ->
  extended_order_limit (fun n => (p n)%:E) q%:E -> forall a,
  a < measure_lp_norm mu N q f -> exists k, forall n, (k <= n)%N -> a < measure_lp_norm mu N (p n) f.
Proof.
move=> hq hp hf hl a ha; case: a ha=> [a| |] ha; last first.
- exists 0%N=> n hn; apply: lt_le_trans (ltNyr 0%R) _.
  exact: (@measure_lp_norm_nonnegative R X V N hN mu (p n) f hm (hp n) hf).
- by move: ha; rewrite ltNge leey.
have [ha0|ha0] := leP 0%R a; last first.
- exists 0%N=> n hn; apply: lt_le_trans (ha0 : a%:E < 0) _.
  exact: (@measure_lp_norm_nonnegative R X V N hN mu (p n) f hm (hp n) hf).
have [he|he] := pselect (exists k, forall n, (k <= n)%N -> a%:E < measure_lp_norm mu N (p n) f); first exact he.
exfalso.
have hbad k : exists n, (k <= n)%N /\ measure_lp_norm mu N (p n) f <= a%:E.
  have [hh|hh] := pselect (exists n, (k <= n)%N /\ measure_lp_norm mu N (p n) f <= a%:E); first exact hh.
  exfalso; apply: he; exists k=> n hn; rewrite ltNge; apply/negP=> hb; apply: hh; exists n; by split.
pose k n := projT1 (cid (hbad n)).
have hk n : (n <= k n)%N /\ measure_lp_norm mu N (p (k n)) f <= a%:E := projT2 (cid (hbad n)).
have hsub : extended_order_limit (fun n => (p (k n))%:E) q%:E.
  split=> b hb.
  - have [j hj] := hl.1 b hb; exists j=> n hn; exact: hj (k n) (leq_trans hn (hk n).1).
  - have [j hj] := hl.2 b hb; exists j=> n hn; exact: hj (k n) (leq_trans hn (hk n).1).
have hbound := @measure_lp_exponent_uniform_bound_closed R X V N hN mu hm f q a (fun n => p (k n))
  hq (fun n => hp (k n)) ha0 hf hsub (fun n => (hk n).2).
by move: ha; rewrite ltNge hbound.
Qed.
