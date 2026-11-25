(** Federer (1969), 2.6.2(4), pp. 115, 117: the signed function identity
    follows from the nonnegative case by 2.4.4(6). Exact partial domains and
    undefined differences of infinities are retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPrecomposition MeasureUP MeasurableFunctionUP CountablyMeasurableUP
  CountablyMeasurableExtendedParts MeasureUpperIntegralPositivePart PartialFunctionIntegralParts
  MeasureIntegralUP MeasureIntegralPartsExist MeasureIntegralPartsDifference MeasureIntegralGraphEquivalence
  ProductMeasure PartialProductSections ParameterizedIntegral ParameterizedIntegralLaws
  ParameterizedIntegralParts NonnegativeProductFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [product_vertical_function_fubini]: complete
    first-coordinate outer-integral identity in Federer 2.6.2(4),
    p. 115, with the signed reduction on p. 117.
    The inner function is defined precisely at integrable sections;
    the outer integrability conclusion supplies its conull domain. *)
Theorem product_vertical_function_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : partial_function (X * Y) (extended_real_line R)) a :
  is_measure_integral (product_measure ha hb) f a ->
  is_countably_measure_measurable_function (product_measure ha hb) (0 : extended_real_line R) f ->
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) a.
Proof.
move=> hf hc; have hnu := product_measure_is_measure ha hb.
have [P [N [hp [hn hd]]]] := (@measure_integral_parts_iff R (X * Y)%type (product_measure ha hb) hnu f a).1 hf.
have [hcp hcn] := @countably_measurable_extended_parts R (X * Y)%type (product_measure ha hb) hnu f hc.
have [hpos hneg] := @partial_parts_nonnegative_almost R (X * Y)%type (product_measure ha hb) hnu f
  (measurable_function_domain hf.1).
have hip := @product_nonnegative_vertical_fubini R X Y alpha beta ha hb
  (partial_extended_function_positive_part f) P hp hcp hpos.
have hin := @product_nonnegative_vertical_fubini R X Y alpha beta ha hb
  (partial_extended_function_negative_part f) N hn hcn hneg.
apply: (@parameterized_integral_from_parts R X Y alpha beta ha hb (partial_product_vertical_section f) P N a _ _ hd).
- apply: (@measure_integral_graph_equivalent R X alpha _ _ P _ hip).
  apply: parameterized_integral_graph_equivalent=> x y z.
  exact: partial_function_precompose_postcompose.
- apply: (@measure_integral_graph_equivalent R X alpha _ _ N _ hin).
  apply: parameterized_integral_graph_equivalent=> x y z.
  exact: partial_function_precompose_postcompose.
Qed.
