(** Federer (1969), 4.1.11, p. 365: the original
    three-factor repeated integral. This adapter iterates
    the preceding partial-domain Fubini theorem 2.6.2(4),
    pp. 115–117. Whole factors are countably measurable;
    no finite-mass or finite-integral premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  PartialProductSections ParameterizedIntegral ParameterizedIntegralLaws
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence
  CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableProduct
  CountablyMeasurableNullModification ProductMeasure ProductFunctionFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [triple_product_vertical_fubini]: the literal
    x,t,y repeated integral of an original partial integrand,
    supporting Federer 4.1.11, p. 365. Inner integrals keep
    exactly their original integrability domains; almost-
    everywhere section integrability follows from Fubini. *)
Theorem triple_product_vertical_fubini (R:realType) (X T Y:choiceType)
    (alpha:set X->\bar R) (rho:set T->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hRho:is_measure rho) (hBeta:is_measure beta)
    (f:partial_function (X*(T*Y)) (extended_real_line R)) a:
  measure_countably_measurable alpha setT->
  measure_countably_measurable rho setT->
  measure_countably_measurable beta setT->
  is_measure_integral (product_measure hAlpha (product_measure_is_measure hRho hBeta)) f a->
  is_measure_integral alpha (parameterized_integral rho (fun x:X=>
    parameterized_integral beta (fun t:T=>
      partial_function_precompose (fun y:Y=>(x,(t,y))) f))) a.
Proof.
move=>hX hT hY hIntegral.
pose inner:=product_measure hRho hBeta.
pose hInner:=product_measure_is_measure hRho hBeta.
pose mu:=product_measure hAlpha hInner.
pose hm:=product_measure_is_measure hAlpha hInner.
have hInnerCount:=@product_whole_countably_measurable R T Y rho beta hRho hBeta hT hY.
have hWhole:=@product_whole_countably_measurable R X (T*Y)%type alpha inner hAlpha hInner hX hInnerCount.
have hCount:=@countably_measurable_function_on_countable_source R (X*(T*Y))%type
  (extended_real_line R) mu hm 0 f (@extended_real_zero_closed R) hWhole hIntegral.1.
have hOuter:=(@product_function_fubini R X (T*Y)%type alpha inner hAlpha hInner f a hIntegral hCount).1.
apply:(@measure_integral_almost_equal R X alpha hAlpha _ _ a hOuter).
apply:(@measure_almost_everywhere_mono R X alpha hAlpha _ _ _
  (measurable_function_domain hOuter.1))=>x [v hGraph].
exists v;split;first exact:hGraph.
apply:(parameterized_integral_specification rho _ x v).2.
have hSection:=(parameterized_integral_specification inner (partial_product_vertical_section f) x v).1 hGraph.
have hSectionCount:=@countably_measurable_function_on_countable_source R (T*Y)%type
  (extended_real_line R) inner hInner 0 (partial_product_vertical_section f x)
  (@extended_real_zero_closed R) hInnerCount hSection.1.
have hIterated:=(@product_function_fubini R T Y rho beta hRho hBeta
  (partial_product_vertical_section f x) v hSection hSectionCount).1.
apply:(@measure_integral_graph_equivalent R T rho _ _ v _ hIterated)=>t w.
apply:parameterized_integral_graph_equivalent=>s y z.
by [].
Qed.
