(** Federer (1969), 2.6.2(3), p. 115, proof pp. 115–117: the complete set
    form of Fubini's theorem. The countable-measurability hypothesis is
    essential; no global sigma-finiteness is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureAlmostUP
  CountablyMeasurableUP MeasureIntegralUP ProductMeasure ProductSections ProductMeasureTranspose
  ProductTransposeMeasurability CountableProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [product_set_fubini]: direct complete Federer 2.6.2(3), p.
    115 Almost-everywhere measurability of both coordinate sections and both
    actual outer integral identities are included. *)
Theorem product_set_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  measure_countably_measurable (product_measure ha hb) S ->
  measure_almost_everywhere alpha [set x | measure_measurable beta (product_vertical_section S x)] /\
  measure_almost_everywhere beta [set y | measure_measurable alpha (product_horizontal_section S y)] /\
  is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section S x))) (product_measure ha hb S) /\
  is_measure_integral beta (partial_function_total (fun y => alpha (product_horizontal_section S y))) (product_measure ha hb S).
Proof.
move=> hS.
have [hv hi] := @product_countably_measurable_vertical_fubini R X Y alpha beta ha hb S hS.
have ht := @product_countably_measurable_transpose R X Y alpha beta ha hb S hS.
have [hh hj] := @product_countably_measurable_vertical_fubini R Y X beta alpha hb ha (product_transpose S) ht.
rewrite product_measure_transpose in hj.
split=> //; split=> //; by split.
Qed.
