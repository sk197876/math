(** Federer (1969), 3.3.4, pp. 289–290:
    apply actual set Fubini to a countably
    measurable incidence whose original vertical
    sections all have zero measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralUniqueness MeasureConullZeroIntegral
  CountablyMeasurableUP ProductMeasure ProductSections ProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_null_sections_product_null]:
    the zero inner-integral step in the
    Haar/Fubini argument of Federer 3.3.4,
    pp. 289–290, by 2.6.2(3), p. 115.
    Actual zero section masses give an
    almost-zero total integrand. Uniqueness
    with the actual Fubini product integral
    proves original product nullity. *)
Theorem structure_null_sections_product_null (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (nu:set Y->\bar R)
    (hMu:is_measure mu) (hNu:is_measure nu) (S:set (X*Y)):
  measure_countably_measurable (product_measure hMu hNu) S ->
  (forall x,nu (product_vertical_section S x)=0%E) ->
  product_measure hMu hNu S=0%E.
Proof.
move=>hS hSections.
have hAlmost:measure_almost_everywhere mu [set x|nu (product_vertical_section S x)=0%E].
  apply:(measure_almost_everywhere_mono hMu _ (measure_almost_everywhere_true hMu)).
  by move=>x _; exact:hSections x.
have hGraph:measure_almost_everywhere mu [set x|
    partial_function_graph
      (partial_function_total (fun x=>nu (product_vertical_section S x))) x 0%E].
  apply:(measure_almost_everywhere_mono hMu _ hAlmost)=>x hx.
  exact:hx.
have hZero:=measure_almost_zero_integral hMu hGraph.
have hFubini:=(@product_set_fubini R X Y mu nu hMu hNu S hS).2.2.1.
exact:measure_integral_unique hFubini hZero.
Qed.
