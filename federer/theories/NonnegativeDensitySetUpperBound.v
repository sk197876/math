(** Federer (1969), 3.2.46, pp. 281–282: supporting
    upper comparison of a density measure with a constant
    multiple of the reference measure. Actual outer masses
    of arbitrary subsets are retained, using 2.4.5, p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic RegularMeasureUP
  MeasureDensityUP MeasureSubsetIntegral MeasureIntegralUP MeasureIntegralBounds
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepIntegralIdentification
  MeasureCharacteristicRegular MeasureUpperIntegralScale MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_density_set_upper_bound]: if
    h<=C on S, its density measure is at most C times the
    original outer mass of S, supporting 3.2.46, pp. 281–282.
    Regularity of the reference measure supplies a true
    equal-mass measurable hull; no null hull difference is assumed. *)
Lemma nonnegative_density_set_upper_bound (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : X -> extended_real_line R) (S : set X) (C : R) :
  is_regular_measure mu -> is_measure_density mu (partial_function_total h) nu ->
  (0<C)%R -> (forall x, S x -> h x<=C%:E) -> nu S<=C%:E*mu S.
Proof.
move=> hRegular hDensity hC hBound.
pose chi := @CharacteristicFunction.value R X S.
have hChi := @CharacteristicFunction.laws R X S.
pose f := partial_real_function_embed (partial_function_total chi).
have hMass := @regular_measure_characteristic_upper_integral R X mu hm S chi hChi hRegular.
rewrite (hDensity S) /measure_subset_upper_integral -hMass
  -(@measure_upper_integral_positive_scale R X mu hm C f hC).
apply: (@measure_upper_integral_monotone R X mu hm).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=> x _.
case: (pselect (S x))=> hx.
- exists (h x),(C%:E*(chi x)%:E); split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split.
    * exists (chi x)%:E; split=> //; exists (chi x); by split.
    * rewrite /chi (characteristic_on_set hChi hx) mule1; exact: hBound x hx.
- exists 0,(C%:E*(chi x)%:E); split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split.
    * exists (chi x)%:E; split=> //; exists (chi x); by split.
    * by rewrite /chi (characteristic_off_set hChi hx) mule0.
Qed.
