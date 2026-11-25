(** Opaque Cartesian product interface for Federer (1969), 2.6.1, pp.
    114–115 The existence construction is private. Source context and
    conventions: ProductMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasureUP ProductMeasureCoverUP ProductMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ProductMeasureSignature.
(** Source for [value]: abstract Cartesian product from
    Federer 2.6.1, pp. 114–115, for two measures. *)
Parameter value : forall (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R),
  is_measure alpha -> is_measure beta -> set (X * Y) -> \bar R.
(** Source for [laws]: abstract infimum and extremal laws for
    Federer 2.6.1, pp. 114–115. *)
Parameter laws : forall (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta),
  is_product_measure alpha beta (@value R X Y alpha beta ha hb) /\
  is_product_cover_infimum alpha beta (@value R X Y alpha beta ha hb).
End ProductMeasureSignature.
Module ProductMeasure : ProductMeasureSignature.
(** Source for [value]: witness selected from proved existence
    for Federer 2.6.1, pp. 114–115, hidden by opaque ascription. *)
Definition value (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :=
  projT1 (cid (product_measure_exists ha hb)).
(** Source for [laws]: the selected witness satisfies the
    abstract laws of Federer 2.6.1, pp. 114–115. *)
Lemma laws (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_product_measure alpha beta (@value R X Y alpha beta ha hb) /\
  is_product_cover_infimum alpha beta (@value R X Y alpha beta ha hb).
Proof. exact: projT2 (cid (product_measure_exists ha hb)). Qed.
End ProductMeasure.
