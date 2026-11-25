(** Concrete infinite gauge supporting Federer (1969), 2.3.8, p. 78, where
    the pseudodistance is expressly allowed to equal infinity. Use counting
    measure on the natural numbers and the real function n |-> n. This
    witness is local, not separately printed in either source. Source
    editions: MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import PartialFunctionBasic CountingMeasure NonnegativeSum ExtendedRealBounds
  MeasureGauge RealNormUP NormMetric MeasurableNormedFunctionUP MeasurableNormedCountableRange FiniteCountingFunctionExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [natural_real_upper_tail_infinite]: every real
    threshold leaves infinitely many natural values above it,
    supporting the infinite pseudodistance allowed in Federer
    2.3.8, p. 78. *)
Lemma natural_real_upper_tail_infinite (R : realType) (r : R) :
  infinite_set [set n : nat | (r < n%:R)%R].
Proof.
pose N := Num.bound (Order.max r 0%R).
have hr : (r < N%:R)%R.
  apply: le_lt_trans _ (archi_boundP _); first by rewrite le_max lexx.
  by rewrite le_max lexx orbT.
move=> hfin.
pose f n := (N+n)%N.
have hi : {in f @^-1` [set n : nat | (r < n%:R)%R] &, injective f}.
  move=> n m _ _; exact: addnI.
have hp := finite_preimage hi hfin.
have he : f @^-1` [set n : nat | (r < n%:R)%R] = setT.
  apply/seteqP; split=> // n _; change (r < (N+n)%:R)%R.
  apply: lt_le_trans hr _; by rewrite ler_nat leq_addr.
apply: infinite_nat; by rewrite he in hp.
Qed.

(** Source for [counting_natural_function_infinite_gauge]: the
    real-valued natural-index function has infinite gauge, supplying
    a concrete witness for Federer 2.3.8, p. 78. *)
Theorem counting_natural_function_infinite_gauge (R : realType) :
  measure_gauge (@counting_measure R nat) (fun y : R => `|y|%R)
    (partial_function_total (fun n : nat => (n%:R : R))) = +oo.
Proof.
apply/eqP; rewrite eq_le leey /=; apply: extended_real_inf_greatest.
move=> t [ht hb]; case: t ht hb=> [r| |] ht hb; last by [].
2: exact: lexx.
have he : partial_norm_superlevel (fun y : R => `|y|%R)
    (partial_function_total (fun n : nat => (n%:R : R))) r%:E = [set n : nat | (r < n%:R)%R].
  apply/seteqP; split=> n.
  - move=> [y [<- hy]]; have hy' : (r < `|n%:R : R|)%R := hy.
    by rewrite normr_nat in hy'.
  - move=> hn; exists (n%:R : R); split=> //; change (r < `|n%:R : R|)%R.
    by rewrite normr_nat.
rewrite he (@counting_measure_infinite R nat [set n : nat | (r < n%:R)%R] (@natural_real_upper_tail_infinite R r)) leNgt ltry in hb.
by [].
Qed.

(** Source for [counting_natural_function_measurable_normed]: the
    infinite-gauge example lies in A(mu,R), as required by
    the pseudodistance assertion in Federer 2.3.8, p. 78.
    Counting measure makes every preimage measurable, and the
    countable range has a separable closed linear span. *)
Lemma counting_natural_function_measurable_normed (R : realType) :
  @is_measurable_normed_function R nat R^o _ (scalar_absolute_value_norm R)
    (@counting_measure R nat) (partial_function_total (fun n : nat => (n%:R : R))).
Proof.
apply: (@measurable_normed_countable_total_range R nat R^o _ (scalar_absolute_value_norm R)
  _ (counting_measure_is_measure R nat)).
- exact: counting_measurable_total_function.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
Qed.
