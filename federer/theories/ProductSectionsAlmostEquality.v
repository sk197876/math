(** Federer (1969), 2.6.2, p. 117: use the null-section result to preserve
    almost equality when fixing one coordinate. This supports the original
    partial domains in (4), p. 115. this functional consequence is
    supporting infrastructure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  ProductMeasure ProductNullSections PartialProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [product_almost_equal_vertical_sections]: supporting
    null-modification transfer for Federer 2.6.2(4), p. 117.
    Product-almost-equal partial functions have almost-equal sections
    for almost every outer coordinate, with no countable-support
    assumption needed for this null-set consequence. *)
Lemma product_almost_equal_vertical_sections (R : realType) (X Y : choiceType) (Z : Type)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f g : partial_function (X * Y) Z) :
  measure_almost_equal (product_measure ha hb) f g ->
  measure_almost_everywhere alpha [set x | measure_almost_equal beta
    (partial_product_vertical_section f x) (partial_product_vertical_section g x)].
Proof.
move=> he; exact (@product_null_vertical_sections R X Y alpha beta ha hb
  (~` partial_function_agreement f g) he).
Qed.
