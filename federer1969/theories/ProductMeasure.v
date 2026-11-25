(** Public Cartesian product of measures for Federer (1969), 2.6.1, pp.
    114–115 Only the sealed laws are used here. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasureUP ProductMeasureCoverUP ProductMeasureSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure]: the Cartesian product of two
    measures defined in Federer 2.6.1, pp. 114–115,
    exposed through its proved abstract specification. *)
Definition product_measure (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) := @ProductMeasure.value R X Y alpha beta ha hb.

(** Source for [product_measure_specification]: the largest-measure
    characterisation in Federer 2.6.1, p. 115 *)
Lemma product_measure_specification (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_product_measure alpha beta (product_measure ha hb).
Proof. exact: (ProductMeasure.laws ha hb).1. Qed.

(** Source for [product_measure_cover_specification]: the covering infimum
    in Federer 2.6.1, pp. 114–115 *)
Lemma product_measure_cover_specification (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_product_cover_infimum alpha beta (product_measure ha hb).
Proof. exact: (ProductMeasure.laws ha hb).2. Qed.

(** Source for [product_measure_is_measure]: Federer 2.6.1, p. 115, first
    assertion *)
Lemma product_measure_is_measure (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) : is_measure (product_measure ha hb).
Proof. exact: product_measure_measure_law (product_measure_specification ha hb). Qed.

(** Source for [product_measure_rectangle_bound]: Federer 2.6.1, p. 115,
    displayed measurable-rectangle inequality *)
Lemma product_measure_rectangle_bound (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  product_measure ha hb (A `*` B) <= alpha A * beta B.
Proof. exact (@product_measure_rectangle_bound_law R X Y alpha beta _ (product_measure_specification ha hb) A B). Qed.

(** Source for [product_measure_greatest]: Federer 2.6.1, p. 115, maximality
    among all measures satisfying the rectangle inequality *)
Lemma product_measure_greatest (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (eta : set (X * Y) -> \bar R) :
  is_measure eta ->
  (forall A B, measure_measurable alpha A -> measure_measurable beta B -> eta (A `*` B) <= alpha A * beta B) ->
  forall S, eta S <= product_measure ha hb S.
Proof. exact (@product_measure_greatest_law R X Y alpha beta _ (product_measure_specification ha hb) eta). Qed.
