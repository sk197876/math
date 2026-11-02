(** Federer (1969), 2.3.9, p. 79: the sets B_j have complements bounded by
    r_j and their union is conull. This supporting measure argument uses
    covering and the numerical tail limit, so measurability of the
    exceptional sets is unnecessary. Source context:
    SummableMetricIncrementBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSequenceTail MeasureUP MeasureBasic
  MeasureIndexedCover MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_exceptional_tail]: the complement
    of B_j in Federer 2.3.9, p. 79, written as a
    union of the exceptional sets from index j onward. *)
Definition summable_exceptional_tail (X : Type) (E : nat -> set X) j :=
  \bigcup_(n in [set n | (j <= n)%N]) E n.

(** Source for [summable_exceptional_tail_bound]: the covering
    estimate mu(X-B_j) <= r_j in Federer 2.3.9, p. 79. *)
Lemma summable_exceptional_tail_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : nat -> set X) (a : nat -> \bar R) :
  (forall n, mu (E n) <= a n) -> forall j,
  mu (summable_exceptional_tail E j) <= nonnegative_sequence_tail a j.
Proof.
move=> he j; apply: le_trans (@measure_indexed_cover R X nat mu hm
  (summable_exceptional_tail E j) [set n | (j <= n)%N] E
  (countableP _) (fun x hx => hx)) _.
apply: nonnegative_sum_mono=> n hn; exact: he.
Qed.

(** Source for [summable_exceptional_tails_null]: direct
    conull-union step in Federer 2.3.9, p. 79. The
    intersection of the exceptional tails has measure zero. *)
Theorem summable_exceptional_tails_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : nat -> set X) (a : nat -> \bar R) :
  (forall n, 0 <= a n) -> nonnegative_sum setT a < +oo ->
  (forall n, mu (E n) <= a n) -> mu (\bigcap_j summable_exceptional_tail E j) = 0.
Proof.
move=> ha hf he; pose C := \bigcap_j summable_exceptional_tail E j.
have hb j : mu C <= nonnegative_sequence_tail a j.
  apply: le_trans (@measure_mono R X mu hm C (summable_exceptional_tail E j) _) _.
  - move=> x hx; exact: hx j Logic.I.
  - exact: summable_exceptional_tail_bound.
have hfin : mu C \is a fin_num.
  rewrite ge0_fin_numE; last exact: measure_nonnegative.
  apply: le_lt_trans (hb 0%N) _.
  have hh := nonnegative_sequence_tail_finite hf 0%N.
  by move: hh; rewrite ge0_fin_numE // nonnegative_sequence_tail_nonnegative.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
rewrite leNgt; apply/negP=> hp.
have hp' : (0 < fine (mu C))%R by rewrite -(fineK hfin) lte_fin in hp.
have [K hK] := nonnegative_sequence_tail_small ha hf hp'.
have hh := le_lt_trans (hb K) (hK K (leqnn K)).
by rewrite fineK // ltxx in hh.
Qed.
