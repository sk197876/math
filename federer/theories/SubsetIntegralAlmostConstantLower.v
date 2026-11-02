(** Federer (1969), 3.2.26(3), p. 262: integrate
    the almost-everywhere lower projection-norm bound on a
    Borel partition member. Use the partial integrand's
    actual values and the characteristic-function integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralComparison
  PartialExtendedOrderLoci SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_almost_positive_constant_lower]:
    supporting integral-order step in 3.2.26(3), p. 262,
    by 2.4.4(5), p. 82. A lower bound by a
    positive constant need hold only on actual integrand
    values at almost every point of the subset; the
    integral already supplies its precise partial domain. *)
Lemma subset_integral_almost_positive_constant_lower (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (u:partial_function X (extended_real_line R)) (a: \bar R) (c:R):
  is_measure mu ->measure_measurable mu A ->(0<c)%R ->
  is_measure_subset_integral mu A u a ->
  measure_almost_everywhere_on mu A [set x|exists z,partial_function_graph u x z /\c%:E<=z] ->
  c%:E*mu A<=a.
Proof.
move=>hMu hA hc hI hLower.
pose chi:=@CharacteristicFunction.value R X A.
have hChi:=@CharacteristicFunction.laws R X A.
pose lo:=real_total_integrand (fun x=>(c*chi x)%R).
have hLo:is_measure_integral mu lo (c%:E*mu A):=
  @measure_positive_characteristic_integral R X mu hMu A chi c hChi hA hc.
apply:(@measure_integral_monotone R X mu hMu lo
  (partial_function_zero_extension (0:extended_real_line R) A u) _ _ hLo hI).
apply:(measure_almost_everywhere_mono hMu _
  ((measure_almost_everywhere_on_implication _ _ _).1 hLower))=>x hBound.
have [hx|hx]:=pselect (A x).
- have [z [hValue hComparison]]:=hBound hx.
  exists c%:E,z; split.
  + rewrite /lo real_total_integrand_graph /chi (characteristic_on_set hChi hx) mulr1.
    reflexivity.
  + split; last exact hComparison.
    apply:(partial_function_zero_extension_on _ _ _ hx).2; exact hValue.
- exists 0,0; split.
  + rewrite /lo real_total_integrand_graph /chi (characteristic_off_set hChi hx) mulr0.
    reflexivity.
  + split; last exact:lexx.
    apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
Qed.
