(** Supporting the two numerical jump sums in Federer (1969), 2.10.14, p.
    177, with the nonnegative numerical sums of 2.1.1, pp. 52–53. Specify a
    measure by the finite-sum supremum laws for its prescribed singleton
    weights. The implementation remains behind an opaque module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumUP NonnegativeSumSealed NonnegativeSum
  WeightedCountingMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_counting_measure_witness]: existence witness
    for the abstract jump-budget measure supporting 2.10.14,
    p. 177. Reuse the sealed numerical sum of 2.1.1,
    pp. 52–53, without exposing this witness downstream. *)
Definition weighted_counting_measure_witness (R : realType) (X : choiceType)
    (w : X -> \bar R) (A : set X) := nonnegative_sum A w.

(** Source for [weighted_counting_measure_witness_laws]: proved
    finite-subsum specification for the witness supporting 2.10.14,
    p. 177. No additional project axiom is introduced. *)
Lemma weighted_counting_measure_witness_laws (R : realType) (X : choiceType)
    (w : X -> \bar R) : is_weighted_counting_measure w (weighted_counting_measure_witness w).
Proof. move=> A; exact: NonnegativeSum.laws. Qed.
