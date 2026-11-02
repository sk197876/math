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
From Federer Require Import MeasureUP MeasureBasic NonnegativeSum ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_hit_measure]: direct measure formula
    in Federer 2.9.18(1), p. 163: the supremum
    of zero and c_j for which A meets S_j. A
    witness point expresses the printed nonempty intersection.
    The formula uses only the existing sealed supremum laws. *)
Definition weighted_hit_measure (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) (A : set X) :=
  extended_real_sup [set y | y=0 \/ exists n x, A x /\ S n x /\ y=(c n)%:E].

(** Source for [weighted_hit_measure_nonnegative]: supporting
    nonnegativity of the measure in Federer 2.9.18(1),
    p. 163. The included zero value makes the formula
    nonnegative, even for auxiliary coefficient sequences not
    assumed positive. The printed example later uses positive c_j. *)
Lemma weighted_hit_measure_nonnegative (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) A : 0<=weighted_hit_measure c S A.
Proof. apply: extended_real_sup_upper; by left. Qed.

(** Source for [weighted_hit_measure_hit]: direct lower bound
    implicit in the supremum formula in Federer 2.9.18(1),
    p. 163: if A meets S_j, its value is at least c_j. *)
Lemma weighted_hit_measure_hit (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) A n :
  (exists x, A x /\ S n x) -> (c n)%:E<=weighted_hit_measure c S A.
Proof. move=> [x [hx hs]]; apply: extended_real_sup_upper; right; by exists n,x. Qed.

(** Source for [weighted_hit_measure_is_measure]: direct assertion
    that the formula defines a measure over X in Federer
    2.9.18(1), p. 163. Each hit point in a
    covered set lies in some covering member; its coefficient
    is bounded by that member's value and hence by the
    nonnegative numerical sum. No Borel regularity is asserted. *)
Theorem weighted_hit_measure_is_measure (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) : is_measure (weighted_hit_measure c S).
Proof.
constructor; first exact: weighted_hit_measure_nonnegative.
move=> A F hF hcover; apply: extended_real_sup_least=> y [->|[n [x [hx [hs ->]]]]].
- exact: nonnegative_sum_nonnegative.
- have [B hB hxB] := hcover x hx.
  apply: le_trans (@weighted_hit_measure_hit R X c S B n (ex_intro _ x (conj hxB hs))) _.
  exact: nonnegative_sum_term hB.
Qed.

(** Source for [weighted_hit_measure_empty]: supporting zero
    empty-set value for the measure in Federer 2.9.18(1),
    p. 163. No coefficient is eligible without an actual
    hit point. This distinguishes the book from the erroneous
    empty-intersection replacement in the erratum cited above. *)
Lemma weighted_hit_measure_empty (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) : weighted_hit_measure c S set0=0.
Proof. exact: measure_empty (weighted_hit_measure_is_measure c S). Qed.
