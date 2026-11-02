(** Federer (1969), 2.6.2, proof pp. 116–117: the hull W is a countable
    intersection of countable unions of measurable rectangles (the class P2
    in the book). We specify the sequential form needed by the actual hull
    construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureCountableClosure ProductMeasure ProductRectangleMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_countable_rectangle_intersection]: the form of W in
    Federer 2.6.2, p. 116 Both sequences may repeat terms; the outer family
    is nonempty. *)
Definition is_countable_rectangle_intersection (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (W : set (X * Y)) :=
  exists (A : nat -> nat -> set X) (B : nat -> nat -> set Y),
    (forall n m, measure_measurable alpha (A n m) /\ measure_measurable beta (B n m)) /\
    W=(\bigcap_n (\bigcup_m (A n m `*` B n m))).

(** Source for [countable_rectangle_intersection_measurable]: every
    constructed P2 hull is product measurable in Federer 2.6.2, p. 117 This
    uses only rectangle measurability and countable closure. *)
Lemma countable_rectangle_intersection_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (W : set (X * Y)) :
  is_countable_rectangle_intersection alpha beta W -> measure_measurable (product_measure ha hb) W.
Proof.
move=> [A [B [hm ->]]].
apply: (@measure_measurable_countable_intersection R (X * Y)%type _ _
  (product_measure_is_measure ha hb) setT _ (countableP setT))=> n _.
apply: (@measure_measurable_countable_union R (X * Y)%type _ _
  (product_measure_is_measure ha hb) setT _ (countableP setT))=> m _.
exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb (A n m) (B n m) (hm n m).1 (hm n m).2).
Qed.
