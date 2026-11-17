(** Federer (1969), 3.4.8(13), p. 336:
    bounded projection multiplicity, supported on an actual
    coordinate ball, bounds its integral. Apply the
    original integral comparison of 2.4.4(5), p. 82,
    and the weighted characteristic integral of 2.4.5,
    p. 83. No source measurability is inferred. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralComparison
  MeasureExtendedCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_support_integral_comparison]: the
    multiplicity integral estimate in the last displayed
    calculation of 3.4.8(13), p. 336. The
    cap is an almost-everywhere bound; the actual
    support is measurable. Infinite integral values are allowed. *)
Theorem bounded_support_integral_comparison (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (f:X->\bar R) (c b: \bar R):
  is_measure mu ->measure_measurable mu A ->0<=c ->
  is_measure_integral mu (partial_function_total f) b ->
  (forall x,~A x ->f x=0) ->
  measure_almost_everywhere mu [set x|f x<=c] ->b<=c*mu A.
Proof.
move=>hMu hA hc hIntegral hSupport hCap.
pose chi:=@CharacteristicFunction.value R X A.
have hChi:=@CharacteristicFunction.laws R X A.
have hUpper:=@measure_nonnegative_extended_characteristic_integral R X mu hMu A chi c hChi hA hc.
apply:(@measure_integral_monotone R X mu hMu _ _ _ _ hIntegral hUpper).
apply:(measure_almost_everywhere_mono hMu _ hCap)=>x hx.
exists (f x),(c*(chi x)%:E);split;first reflexivity.
split;first reflexivity.
case:(pselect (A x))=>hAx.
- by rewrite /chi (characteristic_on_set hChi hAx) mule1.
- by rewrite /chi (hSupport x hAx) (characteristic_off_set hChi hAx) mule0.
Qed.
