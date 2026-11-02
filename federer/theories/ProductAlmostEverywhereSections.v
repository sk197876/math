(** Federer (1969), 3.1.3(4), p. 213: the second use of Fubini
    gives a product-null exceptional set from almost-everywhere null
    horizontal sections. Measurability of the exceptional set is explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasureFiniteClosure MeasureIntegralUniqueness MeasureConullZeroIntegral
  ProductMeasure ProductSections ProductSetFubini CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_almost_everywhere_from_horizontal_sections]:
    the final Fubini step in Federer 3.1.3(4), p. 213, using 2.6.2(3).
    Sigma finiteness of the factor spaces gives the required countable
    measurability of the exceptional set. *)
Theorem product_almost_everywhere_from_horizontal_sections (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (P : set (X*Y)) :
  measure_countably_measurable alpha setT ->
  measure_countably_measurable beta setT ->
  measure_measurable (product_measure ha hb) P ->
  measure_almost_everywhere beta [set y | measure_almost_everywhere alpha
    (product_horizontal_section P y)] ->
  measure_almost_everywhere (product_measure ha hb) P.
Proof.
move=> hca hcb hP hae.
have hc : measure_countably_measurable (product_measure ha hb) (~` P).
  apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb)
    (measure_measurable_complement hP) (fun p _=>Logic.I)).
  exact: product_whole_countably_measurable hca hcb.
have hi := (@product_set_fubini R X Y alpha beta ha hb (~` P) hc).2.2.2.
apply: (measure_integral_unique hi).
exact (@measure_almost_zero_integral R Y beta hb
  (partial_function_total (fun y=>alpha (product_horizontal_section (~` P) y))) hae).
Qed.
