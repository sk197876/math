(** Federer (1969), 2.6.2(4), p. 115, proof p. 117: equality of both
    iterated integrals with the product integral for integrable, countably
    measurable functions. p. 239 leaves the deduction as an exercise. We use
    Federer's characteristic expansion and signed reduction. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP
  CountablyMeasurableUP MeasureIntegralUP MeasureIntegralGraphEquivalence ProductMeasure
  PartialProductSections ProductFunctionTranspose ParameterizedIntegral ParameterizedIntegralLaws
  ProductVerticalFunctionFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [product_function_fubini]: direct two-order identity
    of Federer 2.6.2(4), p. 115, proof p. 117.
    Each inner function has exactly the domain where the section
    is integrable. The theorem asserts actual outer integrability,
    including a conull domain, without imposing sigma-finiteness
    of either factor or finiteness of the integral. *)
Theorem product_function_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : partial_function (X * Y) (extended_real_line R)) a :
  is_measure_integral (product_measure ha hb) f a ->
  is_countably_measure_measurable_function (product_measure ha hb) (0 : extended_real_line R) f ->
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) a /\
  is_measure_integral beta (parameterized_integral alpha (partial_product_horizontal_section f)) a.
Proof.
move=> hf hc; split.
- exact (@product_vertical_function_fubini R X Y alpha beta ha hb f a hf hc).
- have hit := @product_integral_transpose R X Y alpha beta ha hb f a hf.
  have hct := @product_countably_measurable_function_transpose R X Y (extended_real_line R)
    alpha beta ha hb 0 f hc.
  have hi := @product_vertical_function_fubini R Y X beta alpha hb ha (partial_product_transpose f) a hit hct.
  apply: (@measure_integral_graph_equivalent R Y beta _ _ a _ hi).
  apply: parameterized_integral_graph_equivalent=> y x z; by [].
Qed.
