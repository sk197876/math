(** Federer (1969), 2.4.10, p. 85: a
    local density bound on the actual support controls
    the genuine change-of-density integral. This supports
    the target-volume comparison in 3.2.46, p. 282,
    without requiring a globally bounded density. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialDensityProduct
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureDensityUP MeasureDensityNonnegative
  MeasureIntegralComparison MeasureIntegralScaleLaw MeasureUpperIntegralScale
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_local_density_integral_bounds]:
    genuine integral comparison under the local density
    control used in 3.2.46, p. 282, by
    2.4.10, p. 85. The weight may be
    infinite and need only vanish outside the region
    of control. Both measures and their actual density
    law precede this theorem; no coarea equality is assumed. *)
Theorem nonnegative_local_density_integral_bounds (R : realType) (X : choiceType)
    (phi mu : set X -> \bar R) (j : X -> R)
    (u : X -> extended_real_line R) (s d : R) a :
  is_measure phi ->
  is_measure_density phi (partial_function_total (fun x=>(j x)%:E : extended_real_line R)) mu ->
  is_measure_measurable_function phi (partial_function_total (fun x=>(j x)%:E : extended_real_line R)) ->
  (forall x, 0<=j x) -> (forall x, (0<=u x)%E) -> 0<s -> 0<d ->
  (forall x, u x=0%E \/ (j x<=s*d /\ d<=s*j x)) ->
  is_measure_integral phi (partial_function_total u) a ->
  exists b, is_measure_integral mu (partial_function_total u) b /\
    (b<=s%:E*(d%:E*a))%E /\ (d%:E*a<=s%:E*b)%E.
Proof.
move=> hPhi hDensity hJ hJ0 hU0 hs hd hControl hIntegral.
pose J := partial_function_total (fun x=>(j x)%:E : extended_real_line R).
pose U := partial_function_total u.
pose P := partial_density_product U J.
have hUPositive : measure_almost_everywhere phi (partial_extended_nonnegative_locus U).
  apply:(@measure_almost_everywhere_mono R X phi hPhi classical_sets.setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (u x); by split.
have hJPositive x z : partial_function_graph J x z -> (0<=z)%E.
  move=> <-; rewrite lee_fin; exact:hJ0.
have [b [hActual hProduct]] := @measure_density_nonnegative_integrals R X phi mu hPhi J U
  hDensity hJ hJPositive hIntegral.1 hUPositive.
have hConstant := @measure_integral_positive_scale R X phi hPhi d U a hd hIntegral.
have hUpper := @measure_integral_positive_scale R X phi hPhi s
  (partial_extended_function_scale d U) (d%:E*a)%E hs hConstant.
have hLower := @measure_integral_positive_scale R X phi hPhi s P b hs hProduct.
exists b; split; first exact hActual; split.
- apply:(@measure_integral_monotone R X phi hPhi P _ b _ hProduct hUpper).
  apply:(@measure_almost_everywhere_mono R X phi hPhi classical_sets.setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (u x*(j x)%:E)%E,(s%:E*(d%:E*u x))%E; split.
  + apply/partial_density_product_graph; exists (u x),(j x)%:E; by split; last split.
  split.
  + exists (d%:E*u x)%E; split; last by [].
    exists (u x); by split.
  + have [hZero|[hBound _]] := hControl x.
    * by rewrite hZero !mul0e !mule0.
    * have hExtended : ((j x)%:E<=(s*d)%:E)%E by rewrite lee_fin.
      have hScaled := lee_wpmul2l (hU0 x) hExtended.
      by rewrite EFinM muleCA [(u x*d%:E)%E]muleC in hScaled.
- apply:(@measure_integral_monotone R X phi hPhi _ _ _ _ hConstant hLower).
  apply:(@measure_almost_everywhere_mono R X phi hPhi classical_sets.setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (d%:E*u x)%E,(s%:E*(u x*(j x)%:E))%E; split.
  + exists (u x); by split.
  split.
  + exists (u x*(j x)%:E)%E; split; last by [].
    apply/partial_density_product_graph; exists (u x),(j x)%:E; by split; last split.
  + have [hZero|[_ hBound]] := hControl x.
    * by rewrite hZero !mul0e !mule0.
    * have hExtended : (d%:E<=(s*j x)%:E)%E by rewrite lee_fin.
      have hScaled := lee_wpmul2l (hU0 x) hExtended.
      rewrite EFinM in hScaled.
      by rewrite [(u x*d%:E)%E]muleC [(u x*(s%:E*(j x)%:E))%E]muleCA in hScaled.
Qed.
