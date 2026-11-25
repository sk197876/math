(** Federer (1969), 2.6.2, p. 116: the repeated characteristic integral of A
    times B equals alpha(A) beta(B). Infinite factors are allowed with zero
    times infinity equal to zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureSplit CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureExtendedCharacteristicIntegral ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectangle_vertical_section_measurable]:
    supporting section measurability for a rectangle in
    Federer 2.6.2, p. 116; each section is the
    second factor or the empty set. *)
Lemma rectangle_vertical_section_measurable (R : realType) (X Y : choiceType)
    (beta : set Y -> \bar R) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable beta B -> forall x, measure_measurable beta (product_vertical_section (A `*` B) x).
Proof.
move=> hB x; case: (pselect (A x))=> hx.
- by rewrite (product_vertical_rectangle_on B hx).
- rewrite (product_vertical_rectangle_off B hx); exact: measure_measurable_empty.
Qed.

(** Source for [rectangle_vertical_section_integral]: direct rectangle
    repeated-integral calculation in Federer 2.6.2, p. 116 It applies to
    infinite factor measures as well as finite ones. *)
Lemma rectangle_vertical_section_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  is_measure_integral alpha
    (partial_function_total (fun x => beta (product_vertical_section (A `*` B) x))) (alpha A*beta B).
Proof.
move=> hA hB; pose s := @CharacteristicFunction.value R X A.
have hs : is_characteristic_function A s := CharacteristicFunction.laws R A.
have hi := @measure_nonnegative_extended_characteristic_integral R X alpha ha A s (beta B)
  hs hA (measure_nonnegative hb B).
rewrite muleC in hi.
apply: (@measure_integral_graph_equivalent R X alpha _ _ _ _ hi)=> x y.
change (beta B*(s x)%:E = y <-> beta (product_vertical_section (A `*` B) x) = y).
case: (pselect (A x))=> hx.
- by rewrite (characteristic_on_set hs hx) mule1 (product_vertical_rectangle_on B hx).
- by rewrite (characteristic_off_set hs hx) mule0 (product_vertical_rectangle_off B hx) (measure_empty hb).
Qed.
