(** Federer (1969), 3.2.3(2), p. 243: bounded
    Jacobian multiplication preserves the finite signed variation.
    Supporting density comparison, using 2.4.4(5), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialDensityProduct PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralComparison MeasureIntegralScaleLaw
  MeasureDensityUP MeasureChangeOfDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_density_integral_comparison]: supporting
    bounded-Jacobian estimate for the signed approximation in
    Federer 3.2.3(2), p. 243. Infinite nonnegative integrals
    are retained, and no value is assigned off the density domain. *)
Lemma bounded_density_integral_comparison (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (h:partial_function X (extended_real_line R))
    (u:X->extended_real_line R) (C:R) a b:
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  (0<C)%R -> (forall x j,partial_function_graph h x j -> j<=C%:E) ->
  (forall x,0<=u x) ->
  is_measure_integral mu (partial_function_total u) a ->
  is_measure_integral nu (partial_function_total u) b -> b<=C%:E*a.
Proof.
move=>hNu hMeas hPos hC hBound hu hI hN.
have hProd:=(@measure_density_integral_iff R X mu nu hm h (partial_function_total u)
  hNu hMeas hPos hI.1 b).1 hN.
have hScale:=measure_integral_positive_scale hm hC hI.
apply:(measure_integral_monotone hm hProd hScale).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hPos)=>x [j [hj hj0]].
exists (u x*j),(C%:E*u x); split.
- apply/partial_density_product_graph; exists (u x),j; by split=>//; split.
split; first by exists (u x); split.
rewrite (muleC (C%:E) (u x)); apply:lee_wpmul2l; first exact:hu; exact:(hBound x j hj).
Qed.
