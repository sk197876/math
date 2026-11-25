(** Federer (1969), 3.2.11, p. 249: integrate
    the upper-integral slicing estimate over the outer variable.
    The actual parameterized integral domain is retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralComparison
  MeasureTotalPositiveScale ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_iterated_integral_upper_bound]:
    the outer integration of the 2.10.25 estimate in
    Federer 3.2.11, p. 249. No measurability
    of every individual section is assumed: its actual
    integral exists wherever the outer graph is defined. *)
Theorem coarea_iterated_integral_upper_bound (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R) (ha:is_measure alpha)
    (F:X->partial_function Y (extended_real_line R))
    (theta:X->extended_real_line R) a b (K:R):
  (0<K)%R ->
  is_measure_integral alpha (parameterized_integral beta F) a ->
  is_measure_integral alpha (partial_function_total theta) b ->
  (forall x,measure_upper_integral beta (F x)<=K%:E*theta x) ->
  a<=K%:E*b.
Proof.
move=>hK hF ht hBound.
have hScaled:=measure_total_positive_scale_integral ha hK ht.
apply:(measure_integral_monotone ha hF hScaled).
apply:(@measure_almost_everywhere_mono R X alpha ha _ _ _
  (measurable_function_domain hF.1))=>x [t hGraph].
have hInner:=(parameterized_integral_specification beta F x t).1 hGraph.
have hValue:=measure_upper_integral_unique (measure_upper_integral_specification beta (F x)) hInner.2.1.
exists t,(K%:E*theta x); split=> //; split; first by [].
by rewrite -hValue; exact:hBound.
Qed.
