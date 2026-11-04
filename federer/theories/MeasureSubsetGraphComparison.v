(** Federer (1969), 2.4.4(5), p. 82, and
    2.4.10, p. 85: compare genuine original subset
    integrals by a local bound on their exact partial
    graphs. This supports the frozen coarea inequalities
    of 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialZeroExtension PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralComparison MeasureIntegralScaleLaw MeasurableExtendedScale
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_subset_graph_integral_comparison]:
    the comparison of actual subset integrals used in
    3.2.46, p. 282, from 2.4.4(5), p. 82.
    Exact graph witnesses are required only on S
    almost everywhere; no value outside the original
    partial domains or finite integral bound is supplied. *)
Lemma measure_subset_graph_integral_comparison (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (S : set X)
    (F G : partial_function X (extended_real_line R)) (c : R) a b :
  is_measure mu -> 0<c -> is_measure_subset_integral mu S F a ->
  is_measure_subset_integral mu S G b ->
  measure_almost_everywhere mu [set x | S x -> exists u v,
    partial_function_graph F x u /\ partial_function_graph G x v /\ (u<=c%:E*v)%E] ->
  (a<=c%:E*b)%E.
Proof.
move=> hMu hc hF hG hBound.
have hScaled := @measure_integral_positive_scale R X mu hMu c
  (partial_function_zero_extension (0 : extended_real_line R) S G) b hc hG.
apply:(@measure_integral_monotone R X mu hMu _ _ a (c%:E*b)%E hF hScaled).
apply:(@measure_almost_everywhere_mono R X mu hMu _ _ _ hBound)=> x hx.
case:(pselect (S x))=> hS.
- have [u [v [hu [hv hCompare]]]] := hx hS.
  exists u,(c%:E*v)%E; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split; last exact hCompare.
    exists v; split; last by [].
    apply/partial_function_zero_extension_graph; left; by split.
- exists 0%E,0%E; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split; last exact:lexx.
    exists 0%E; split; last by rewrite mule0.
    apply/partial_function_zero_extension_graph; right; by split.
Qed.
