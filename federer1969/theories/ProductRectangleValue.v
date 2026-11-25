(** Federer (1969), 2.6.2(2), p. 115, proof pp. 116–117: measurable
    rectangles have product measure equal to the product of the two factor
    measures. The lower bound is derived directly from the rectangle-cover
    infimum using the nonnegative integral comparison, a proof-order
    variation explained in ProductRectangleCoverLowerBound.v. No finiteness
    or sigma-finiteness assumption is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure ProductMeasureSequenceInfimum
  ProductRectangleMeasurability ProductRectangleCoverLowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_rectangle_value]: direct equality
    in Federer 2.6.2(2), p. 115; proof p. 116.
    Infinite values and the convention zero times infinity equals
    zero are included. *)
Theorem product_measure_rectangle_value (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  product_measure ha hb (A `*` B) = alpha A * beta B.
Proof.
move=> hA hB; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@product_measure_rectangle_bound R X Y alpha beta ha hb A B hA hB).
- apply: (product_measure_sequence_cover_greatest ha hb)=> C D hm hc.
  exact (@product_rectangle_cover_cost_lower R X Y alpha beta ha hb A B C D hA hB hm hc).
Qed.

(** Source for [product_measure_measurable_rectangle]: full
    Federer 2.6.2(2), p. 115: both measurability and the
    exact value on a rectangle with measurable factors. *)
Theorem product_measure_measurable_rectangle (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  measure_measurable (product_measure ha hb) (A `*` B) /\
  product_measure ha hb (A `*` B) = alpha A * beta B.
Proof.
move=> hA hB; split.
- exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb A B hA hB).
- exact (@product_measure_rectangle_value R X Y alpha beta ha hb A B hA hB).
Qed.
