(** Federer (1969), 2.6.2(3), pp. 115, 117: both orders of the Fubini set
    formula for a product-null set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasureIntegralUP ProductMeasure ProductSections ProductMeasureTranspose ProductNullSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_null_horizontal_sections]: the second
    coordinate order of Federer's null-section assertion in
    2.6.2, p. 117, by the symmetry of the two
    formulas in (3), p. 115. *)
Corollary product_null_horizontal_sections (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure ha hb S = 0 ->
  measure_almost_everywhere beta [set y | alpha (product_horizontal_section S y) = 0].
Proof.
move=> hz; have ht : product_measure hb ha (product_transpose S) = 0.
  by rewrite product_measure_transpose hz.
exact (@product_null_vertical_sections R Y X beta alpha hb ha (product_transpose S) ht).
Qed.

(** Source for [product_null_fubini]: complete null-set case of Federer
    2.6.2(3), pp. 115, 117 Both section measurability statements and both
    actual outer integrals are concluded. The general finite and countably
    measurable cases are separate results. *)
Theorem product_null_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure ha hb S = 0 ->
  measure_almost_everywhere alpha [set x | measure_measurable beta (product_vertical_section S x)] /\
  measure_almost_everywhere beta [set y | measure_measurable alpha (product_horizontal_section S y)] /\
  is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section S x))) 0 /\
  is_measure_integral beta (partial_function_total (fun y => alpha (product_horizontal_section S y))) 0.
Proof.
move=> hz; have ht : product_measure hb ha (product_transpose S) = 0.
  by rewrite product_measure_transpose hz.
split; first exact (@product_null_vertical_sections_measurable R X Y alpha beta ha hb S hz).
split; first exact (@product_null_vertical_sections_measurable R Y X beta alpha hb ha (product_transpose S) ht).
split.
- exact (@product_null_vertical_section_integral R X Y alpha beta ha hb S hz).
- exact (@product_null_vertical_section_integral R Y X beta alpha hb ha (product_transpose S) ht).
Qed.
