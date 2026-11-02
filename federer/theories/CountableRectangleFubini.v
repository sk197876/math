(** Federer (1969), 2.6.2, p. 116: P1 is contained in the
    repeated-integrability class, and the repeated integral on P1 equals the
    product measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP
  ProductMeasure ProductSections DisjointRectangleCoverUP CountableRectangleRefinement
  DisjointRectangleFubini CountableRectangleUnionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_rectangle_union_vertical_integral]: direct P1
    integral equality in Federer 2.6.2, p. 116 The union may have infinite
    measure. The proof uses the abstract disjoint-cover laws of a
    refinement, not its particular construction. *)
Theorem countable_rectangle_union_vertical_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  is_countable_rectangle_union alpha beta S ->
  is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section S x)))
    (product_measure ha hb S).
Proof.
move=> [A [B [hm ->]]].
have [G [hc hg]] := @countable_disjoint_rectangle_refinement R X Y alpha beta ha hb A B hm.
exact (@disjoint_rectangle_cover_vertical_integral R X Y alpha beta ha hb G _ hc hg).
Qed.
