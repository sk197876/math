(** Federer (1969), 2.5.10, p. 101: the geometric obstruction to L^2
    measurability of the representing density. This module isolates the
    Fubini contradiction: zero vertical sections cannot coexist with
    positive horizontal sections on a set of positive measure. The product
    facts are 2.6.2(3), p. 115, proof p. 117. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureConullZeroIntegral ProductMeasure ProductSections ProductSetFubini
  ProductNullFubini CountablyMeasurableUP CountablyMeasurableSubsets CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_vertical_sections_null]: supporting
    Fubini inference for Federer 2.5.10, p. 101,
    by 2.6.2(3), pp. 115, 117. The required
    countable measurability is retained explicitly. *)
Lemma zero_vertical_sections_null (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X*Y)) :
  measure_countably_measurable (product_measure ha hb) S ->
  (forall x, beta (product_vertical_section S x)=0) -> product_measure ha hb S=0.
Proof.
move=> hS hv; have [_ [_ [hi _]]] := @product_set_fubini R X Y alpha beta ha hb S hS.
apply: (measure_integral_unique hi); apply: (measure_almost_zero_integral ha).
apply: (@measure_almost_everywhere_mono R X alpha ha setT _ _ (measure_almost_everywhere_true ha))=> x _.
exact: hv.
Qed.

(** Source for [incompatible_positive_horizontal_sections]:
    the Fubini contradiction implicit in the final
    geometric claim of Federer 2.5.10, p. 101.
    The hypotheses describe the level set of a putative
    L^2 measurable density; this supporting lemma
    does not itself assume or assert such a density. *)
Theorem incompatible_positive_horizontal_sections (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X*Y)) (I : set Y) :
  measure_countably_measurable (product_measure ha hb) S ->
  (forall x, beta (product_vertical_section S x)=0) ->
  (forall y, I y -> 0<alpha (product_horizontal_section S y)) ->
  0<beta I -> False.
Proof.
move=> hS hv hh hI.
have hz := @zero_vertical_sections_null R X Y alpha beta ha hb S hS hv.
have haeh := @product_null_horizontal_sections R X Y alpha beta ha hb S hz.
have hI0 : beta I=0.
  apply: (@measure_null_subset R Y beta hb I
    (~` [set y | alpha (product_horizontal_section S y)=0]) _ haeh).
  move=> y hy hzero; have hpos := hh y hy; by rewrite hzero ltxx in hpos.
by rewrite hI0 ltxx in hI.
Qed.
