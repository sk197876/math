(** Federer (1969), 2.6.3(3), p. 118: the rectangle T has a repeated
    integral, whereas A1 times a nonmeasurable B does not when alpha(A1)>0.
    we retain Federer's order. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureBasic MeasureSplit MeasureIntegralUP MeasureExtendedCharacteristicIntegral ProductSections
  RepeatedIntegralSetUP RepeatedIntegralMeasurableSections PositiveCharacteristicMeasurability SwitchedRectangleSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectangle_horizontal_sections_measurable]: supporting
    measurable inner sections for both rectangles in Federer
    2.6.3(3), p. 118; no measurability of B is required. *)
Lemma rectangle_horizontal_sections_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (ha : is_measure alpha) (A : set X) (B : set Y) :
  measure_measurable alpha A -> forall y, measure_measurable alpha (product_horizontal_section (A `*` B) y).
Proof.
move=> hA y; case: (pselect (B y))=> hy.
- by rewrite (rectangle_horizontal_section_on A hy).
- rewrite (rectangle_horizontal_section_off A hy); exact: measure_measurable_empty.
Qed.

(** Source for [rectangle_horizontal_measure_characteristic]:
    supporting computation of the inner-integral function for
    A1 times B in Federer 2.6.3(3), p. 118. *)
Lemma rectangle_horizontal_measure_characteristic (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (ha : is_measure alpha) (A : set X) (B : set Y) (s : Y -> R) :
  is_characteristic_function B s -> forall y,
    alpha (product_horizontal_section (A `*` B) y) = alpha A*(s y)%:E.
Proof.
move=> hs y; case: (pselect (B y))=> hy.
- by rewrite (rectangle_horizontal_section_on A hy) (characteristic_on_set hs hy) mule1.
- by rewrite (rectangle_horizontal_section_off A hy) (measure_empty ha) (characteristic_off_set hs hy) mule0.
Qed.

(** Source for [repeated_rectangle_integrable]: the assertion
    T belongs to P0 and hence F in Federer 2.6.3(3),
    p. 118, from the rectangle computation on p. 116.
    Both factor measures may be infinite. *)
Lemma repeated_rectangle_integrable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B -> is_repeatedly_integrable_set alpha beta (A `*` B).
Proof.
move=> hA hB; apply: (@repeated_integral_measurable_sections_iff R X Y alpha beta ha (A `*` B)
  (@rectangle_horizontal_sections_measurable R X Y alpha ha A B hA)).2.
pose s := @CharacteristicFunction.value R Y B; have hs := @CharacteristicFunction.laws R Y B.
have he : (fun y => alpha (product_horizontal_section (A `*` B) y)) = (fun y => alpha A*(s y)%:E).
  apply: funext=> y; exact (@rectangle_horizontal_measure_characteristic R X Y alpha ha A B s hs y).
rewrite he; exists (alpha A*beta B).
exact (@measure_nonnegative_extended_characteristic_integral R Y beta hb B s (alpha A) hs hB (measure_nonnegative ha A)).
Qed.

(** Source for [repeated_positive_rectangle_requires_measurability]:
    failure of the repeated integral of A1 times B in
    Federer 2.6.3(3), p. 118. Strict positivity, including
    infinite alpha(A1), makes the positive preimage exactly B. *)
Lemma repeated_positive_rectangle_requires_measurability (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (A : set X) (B : set Y) :
  measure_measurable alpha A -> 0 < alpha A ->
  is_repeatedly_integrable_set alpha beta (A `*` B) -> measure_measurable beta B.
Proof.
move=> hA hp hF.
have [a hi] := (@repeated_integral_measurable_sections_iff R X Y alpha beta ha (A `*` B)
  (@rectangle_horizontal_sections_measurable R X Y alpha ha A B hA)).1 hF.
pose s := @CharacteristicFunction.value R Y B; have hs := @CharacteristicFunction.laws R Y B.
have he : (fun y => alpha (product_horizontal_section (A `*` B) y)) = (fun y => alpha A*(s y)%:E).
  apply: funext=> y; exact (@rectangle_horizontal_measure_characteristic R X Y alpha ha A B s hs y).
rewrite he in hi.
exact (@positive_characteristic_measurable_set R Y beta B s (alpha A) hs hp hi.1).
Qed.
