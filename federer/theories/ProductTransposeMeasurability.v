(** Federer (1969), 2.6.2(3), p. 115: exchange the factors to obtain both
    orders of the set formula. These supporting laws show that the
    measurability and countable- measurability hypotheses are preserved by
    the exchange. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP CountablyMeasurableUP CountablyMeasurableSequences
  ProductMeasure ProductMeasureTranspose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_transpose_union]: supporting coordinate-
    exchange law for the countable families in Federer 2.6.2,
    p. 117. The set identity holds for arbitrary index sets. *)
Lemma product_transpose_union (X Y J : Type) (D : set J) (F : J -> set (X * Y)) :
  product_transpose (\bigcup_(j in D) F j) = \bigcup_(j in D) product_transpose (F j).
Proof. by []. Qed.

(** Source for [product_transpose_intersection]: supporting
    coordinate-exchange law for the measurable-set splitting
    condition used in Federer 2.6.2, pp. 115–117. *)
Lemma product_transpose_intersection (X Y : Type) (S T : set (X * Y)) :
  product_transpose (S `&` T) = product_transpose S `&` product_transpose T.
Proof. by []. Qed.

(** Source for [product_transpose_difference]: supporting
    coordinate-exchange law for the measurable-set splitting
    condition used in Federer 2.6.2, pp. 115–117. *)
Lemma product_transpose_difference (X Y : Type) (S T : set (X * Y)) :
  product_transpose (S `\` T) = product_transpose S `\` product_transpose T.
Proof. by []. Qed.

(** Source for [product_measurable_transpose]: supporting preservation of
    measurability when interchanging the factors in Federer 2.6.2(3), p. 115 *)
Lemma product_measurable_transpose (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  measure_measurable (product_measure ha hb) S ->
  measure_measurable (product_measure hb ha) (product_transpose S).
Proof.
move=> hS T.
rewrite -(@product_measure_transpose R Y X beta alpha hb ha T)
  -(@product_measure_transpose R Y X beta alpha hb ha (T `&` product_transpose S))
  -(@product_measure_transpose R Y X beta alpha hb ha (T `\` product_transpose S))
  product_transpose_intersection product_transpose_difference product_transpose_involutive.
exact: hS.
Qed.

(** Source for [product_countably_measurable_transpose]: supporting
    preservation of the exact hypothesis of Federer 2.6.2(3), p. 115, under
    the symmetry. Transpose each finite measurable piece. *)
Lemma product_countably_measurable_transpose (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  measure_countably_measurable (product_measure ha hb) S ->
  measure_countably_measurable (product_measure hb ha) (product_transpose S).
Proof.
move=> hS; have [F [he hF]] := (countably_measurable_sequence_iff (product_measure_is_measure ha hb) S).1 hS.
apply: (countably_measurable_sequence_iff (product_measure_is_measure hb ha) _).2.
exists (fun n => product_transpose (F n)); split; first by rewrite he product_transpose_union.
move=> n; split.
- exact (@product_measurable_transpose R X Y alpha beta ha hb (F n) (hF n).1).
- by rewrite product_measure_transpose; exact: (hF n).2.
Qed.
