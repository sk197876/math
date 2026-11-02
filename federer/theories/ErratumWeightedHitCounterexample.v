(** Federer (1969), 2.9.18(1), p. 163: sharpness of the upper-limit
    conclusion. The printed book uses nonempty intersection in the
    weighted-hit formula. The May 1987 erratum, p. 3, book p. 163 line 11,
    instead prints empty intersection; the original scan confirms that
    reading. The local counterexample below shows that this replacement
    would give the empty set positive value, so the book's
    nonempty-intersection condition is retained. This is a correction to the
    erratum, not a transcription change. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_miss_capacity]: local correction witness
    for Federer 2.9.18(1), p. 163, and the
    erratum p. 3, book p. 163 line 11. This
    expression applies the erratum's empty-intersection condition
    literally. It is deliberately called a capacity, without
    asserting the measure laws that the book's formula satisfies. *)
Definition weighted_miss_capacity (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) (A : set X) :=
  extended_real_sup [set y | y=0 \/ exists n, A `&` S n=set0 /\ y=(c n)%:E].

(** Source for [weighted_miss_capacity_empty_positive]: local
    counterexample to the replacement in Federer's erratum p. 3,
    book p. 163 line 11, concerning 2.9.18(1).
    If the first coefficient is positive, the empty set
    already has positive value because it misses every S_j. *)
Lemma weighted_miss_capacity_empty_positive (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) : (0<c 0%N)%R ->
  0<weighted_miss_capacity c S set0.
Proof.
move=> hc.
have hterm : (c 0%N)%:E<=weighted_miss_capacity c S set0.
  apply: extended_real_sup_upper; right; exists 0%N; split; first exact: set0I.
  reflexivity.
apply: lt_le_trans _ hterm; by rewrite lte_fin.
Qed.

(** Source for [weighted_miss_capacity_not_measure]: local
    counterexample showing why the book's nonempty-intersection
    condition in Federer 2.9.18(1), p. 163,
    is retained despite erratum p. 3, book p. 163
    line 11. Positive empty-set value contradicts a proved
    consequence of the measure axioms; the scan's wording
    is preserved in the LaTeX transcription. *)
Theorem weighted_miss_capacity_not_measure (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) : (0<c 0%N)%R ->
  ~ is_measure (weighted_miss_capacity c S).
Proof.
move=> hc hm; have hp := @weighted_miss_capacity_empty_positive R X c S hc.
by rewrite (measure_empty hm) ltxx in hp.
Qed.
