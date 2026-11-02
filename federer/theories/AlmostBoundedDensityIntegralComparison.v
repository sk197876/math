(** Federer (1969), 3.2.22(3), p. 260:
    almost-everywhere bounded density suffices to
    preserve a finite signed variation. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialDensityProduct
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralComparison MeasureIntegralScaleLaw MeasureDensityUP MeasureChangeOfDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [almost_bounded_density_integral_comparison]:
    supporting finite-side control in the standard
    approximation of Federer 3.2.22(3), p. 260.
    The 2.4.4(5), p. 82, comparison ignores
    exceptional null values of the density. No
    stronger everywhere bound or summability premise
    is necessary, including when one integral is infinite. *)
Lemma almost_bounded_density_integral_comparison (R:realType) (X:choiceType)
    (rho nu:set X->\bar R) (hr:is_measure rho)
    (h:partial_function X (extended_real_line R)) (u:X->extended_real_line R) (C:R) a b:
  is_measure_density rho h nu ->is_measure_measurable_function rho h ->
  measure_almost_everywhere rho (partial_extended_nonnegative_locus h) ->
  (0<C)%R ->measure_almost_everywhere rho [set x|forall j,partial_function_graph h x j ->j<=C%:E] ->
  (forall x,0<=u x) ->is_measure_integral rho (partial_function_total u) a ->
  is_measure_integral nu (partial_function_total u) b ->b<=C%:E*a.
Proof.
move=>hDensity hMeas hPos hC hBound hu hI hN.
have hProduct:=(@measure_density_integral_iff R X rho nu hr h (partial_function_total u)
  hDensity hMeas hPos hI.1 b).1 hN.
have hScale:=measure_integral_positive_scale hr hC hI.
apply:(measure_integral_monotone hr hProduct hScale).
apply:(measure_almost_everywhere_mono hr _ (measure_almost_everywhere_and hr hPos hBound))=>x [[j [hj hjPositive]] hBx].
exists (u x*j),(C%:E*u x); split.
- apply/partial_density_product_graph; exists (u x),j; by split=>//; split.
split; first by exists (u x); split.
rewrite (muleC (C%:E) (u x)); exact:(lee_wpmul2l (hu x) (hBx j hj)).
Qed.
