(** Federer (1969), 2.4.17, p. 90: continuity at a finite limiting exponent,
    approached through finite exponents in P. Finite limiting norms use a
    summable bracket and Lebesgue convergence; infinite limiting norms use
    Fatou's eventual lower bounds. This supporting sequence theorem includes
    endpoints excluded from P. The extended-exponent topology and infinity
    endpoint are assembled separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP MeasureLpNorm
  ExtendedRealOrderLimit ExtendedOrderLimitShift RealSequenceEventualBracket
  MeasureLpExponentContinuity MeasureLpExponentLowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_exponent_sequence_continuity]: finite
    limiting-exponent case of Federer 2.4.17, p. 90 The limiting norm may be
    infinite; all approaching norms are finite. *)
Theorem measure_finite_exponent_sequence_continuity (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (q : R) (p : nat -> R) :
  (1 <= q)%R -> (forall n, (1 <= p n)%R) -> is_measure_measurable_function mu f ->
  (forall n, measure_lp_norm mu N (p n) f < +oo) ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  extended_order_limit (fun n => measure_lp_norm mu N (p n) f) (measure_lp_norm mu N q f).
Proof.
move=> hq hp hf hfin hl.
have [hqfin|hqfin] := ltP (measure_lp_norm mu N q f) +oo; last first.
- split.
  + exact: (@measure_lp_exponent_eventual_lower_bound R X V N hN mu hm f q p hq hp hf hl).
  + move=> b hb; have hh := le_lt_trans hqfin hb; by move: hh; rewrite ltNge leey.
pose A : set R := [set r | (1 <= r)%R /\ measure_lp_norm mu N r f < +oo].
have hAq : A q by split.
have hAp n : A (p n) by split.
have [s [t [k [hs [ht [hsq [hqt hbound]]]]]]] := @real_sequence_eventual_bracket R A p q hAq hAp hl.
have htail := @extended_order_limit_shift R (fun n => (p n)%:E) q%:E k hl.
have hbr n : (s <= p (k+n)%N)%R /\ (p (k+n)%N <= t)%R.
  apply: hbound; exact: leq_addr.
have hh := @measure_lp_exponent_bracket_continuity R X V N hN mu hm f s t q (fun n => p (k+n)%N)
  hs.1 hsq hqt hbr hf hs.2 ht.2 htail.
exact: (@extended_order_limit_of_shift R (fun n => measure_lp_norm mu N (p n) f) _ k hh).
Qed.
