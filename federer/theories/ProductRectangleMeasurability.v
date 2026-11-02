(** Federer (1969), 2.6.2(2), pp. 115–117: products of measurable factor
    sets are measurable for the Cartesian product measure. This module
    proves only measurability; the exact rectangle value is a separate
    assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteClosure ProductMeasure ProductFirstCylinder ProductSecondCylinder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [product_measure_rectangle_measurable]: the measurability
    assertion of Federer 2.6.2(2), pp. 115–117 Intersect the two measurable
    cylinders obtained by the printed rectangle splits. *)
Theorem product_measure_rectangle_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  measure_measurable (product_measure ha hb) (A `*` B).
Proof.
move=> hA hB.
have hh := @measure_measurable_intersection R (X * Y)%type (product_measure ha hb)
  (product_measure_is_measure ha hb) (A `*` setT) (setT `*` B)
  (product_first_cylinder_measurable ha hb hA) (product_second_cylinder_measurable ha hb hB).
have he : (A `*` setT) `&` (setT `*` B)=A `*` B.
  apply/seteqP; split=> [[x y] [[hx _] [_ hy]]|[x y] [hx hy]]; by split=> //; split.
by rewrite he in hh.
Qed.
