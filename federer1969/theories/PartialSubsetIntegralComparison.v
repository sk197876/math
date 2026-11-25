(** Federer (1969), 2.4.4(3),(5), p. 82, and 2.4.10,
    p. 85: comparison of actual partial subset integrals after
    positive scaling. This supports the local length comparisons
    in 3.2.46, p. 281, without filling missing derivative values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension PartialExtendedOrderLoci PartialExtendedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureSubsetIntegral MeasureIntegralComparison MeasureIntegralScaleLaw
  MeasureUpperIntegralScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_partial_integral_positive_comparison]:
    integration of a local positive-factor bound as used in
    Federer 3.2.46, p. 281, by 2.4.4(3),(5), p. 82.
    Original partial domains and infinite integral values are kept. *)
Lemma subset_partial_integral_positive_comparison (R : realType)
    (X : choiceType) (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u v : partial_function X (extended_real_line R)) (c : R) a b :
  (0 < c)%R -> is_measure_subset_integral mu A u a ->
  is_measure_subset_integral mu A v b ->
  measure_almost_everywhere_on mu A
    (partial_extended_le_locus u (partial_extended_function_scale c v)) ->
  a <= c%:E*b.
Proof.
move=> hc hU hV hBound.
have hScaled := measure_integral_positive_scale hm hc hV.
apply: (measure_integral_monotone hm hU hScaled).
apply: (measure_almost_everywhere_mono hm _
  ((measure_almost_everywhere_on_implication _ _ _).1 hBound)).
move=> x hBx; case: (pselect (A x))=> hx.
- have [r [s [hr [[w [hw hScale]] hLe]]]] := hBx hx.
  exists r,s; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split=> //; exists w; split=> //.
    apply/partial_function_zero_extension_graph; left; by split.
- exists 0,0; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split; last exact: lexx.
    exists 0; split; last by rewrite mule0.
    apply/partial_function_zero_extension_graph; right; by split.
Qed.
