(** Supporting the two numerical jump sums in Federer (1969), 2.10.14, p.
    177, with the nonnegative numerical sums of 2.1.1, pp. 52–53. Specify a
    measure by the finite-sum supremum laws for its prescribed singleton
    weights. The implementation remains behind an opaque module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumUP NonnegativeSumSealed NonnegativeSum
  NonnegativeSumSupport NonnegativeSumRestriction NonnegativeSumCover WeightedCountingMeasureUP
  WeightedCountingMeasureSealed MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_counting_measure]: public atomic measure
    for the numerical jump sums of 2.10.14, p. 177.
    Its implementation is accessed only through the abstract
    finite-sum laws, as for counting measure in 2.1.2, p. 54. *)
Definition weighted_counting_measure (R : realType) (X : choiceType)
    (w : X -> \bar R) := @WeightedCountingMeasure.value R X w.

(** Source for [weighted_counting_measure_specification]: proved
    universal laws of the atomic jump budget in 2.10.14,
    p. 177, supplied by the sealed existence witness. *)
Lemma weighted_counting_measure_specification (R : realType) (X : choiceType)
    (w : X -> \bar R) : is_weighted_counting_measure w (weighted_counting_measure w).
Proof. exact: WeightedCountingMeasure.laws. Qed.

(** Source for [weighted_counting_measure_sum]: supporting numerical-
    sum formula for the jump sums in 2.10.14, p. 177,
    derived from uniqueness of the specification of 2.1.1,
    pp. 52–53, rather than by unfolding the sealed witness. *)
Lemma weighted_counting_measure_sum (R : realType) (X : choiceType)
    (w : X -> \bar R) (A : set X) :
  weighted_counting_measure w A=nonnegative_sum A w.
Proof.
exact: (@nonnegative_sum_unique R X A w _ _
  (weighted_counting_measure_specification w A) (NonnegativeSum.laws A w)).
Qed.

(** Source for [weighted_counting_measure_is_measure]: supporting
    measure law for the jump budgets in 2.10.14, p. 177.
    The numerical covering inequality of 2.1.1, pp. 52–53,
    proves the outer-measure law without a countable-support premise. *)
Lemma weighted_counting_measure_is_measure (R : realType) (X : choiceType)
    (w : X -> \bar R) : (forall x, 0<=w x) -> is_measure (weighted_counting_measure w).
Proof.
move=> hw; constructor; first by move=> A; rewrite weighted_counting_measure_sum; exact: nonnegative_sum_nonnegative.
move=> A F hF hcov; rewrite weighted_counting_measure_sum.
have he : nonnegative_sum F (weighted_counting_measure w)=
    nonnegative_sum F (fun B => nonnegative_sum B w).
  by apply: nonnegative_sum_ext=> B hB; rewrite weighted_counting_measure_sum.
rewrite he; exact: (@nonnegative_sum_cover R X [the choiceType of set X] A F (fun B => B) w hw hcov).
Qed.

(** Source for [weighted_counting_measure_measurable]: supporting
    additivity on all parameter sets for the jump budgets of
    2.10.14, p. 177. Numerical-sum splitting, 2.1.1,
    p. 53, shows that every set is measurable. *)
Lemma weighted_counting_measure_measurable (R : realType) (X : choiceType)
    (w : X -> \bar R) (A : set X) : (forall x, 0<=w x) ->
  measure_measurable (weighted_counting_measure w) A.
Proof.
move=> hw T; rewrite !weighted_counting_measure_sum.
apply: nonnegative_sum_split=> x hx; exact: hw.
Qed.
