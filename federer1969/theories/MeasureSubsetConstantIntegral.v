(** Federer (1969), 2.4.10, p. 85, used for
    the constant Jacobian and fibre integrals in 3.2.28,
    pp. 265–267: the integral of a nonnegative
    constant over a measurable set is its measure
    times that constant, including infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_nonnegative_constant_subset_integral]:
    the constant-integrand evaluations in Federer
    3.2.28, pp. 265–267, by 2.4.10,
    p. 85, and the characteristic-function integral
    of 2.4.5, p. 83. The zero-infinity
    convention is preserved and no finite-mass premise
    is added. *)
Theorem measure_nonnegative_constant_subset_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (c : \bar R):
  is_measure mu ->measure_measurable mu A ->0<=c ->
  is_measure_subset_integral mu A (partial_function_total (fun _ : X=>(c:extended_real_line R))) (c*mu A).
Proof.
move=>hMu hA hc.
pose chi:=@CharacteristicFunction.value R X A.
have hChi:=@CharacteristicFunction.laws R X A.
have hI:=@measure_nonnegative_extended_characteristic_integral R X mu hMu A chi c hChi hA hc.
apply:measure_integral_graph_equivalent _ hI=>x z.
rewrite partial_function_zero_extension_graph.
change (c*(chi x)%:E=z <->(A x /\c=z) \/(~A x /\z= 0)).
case:(pselect (A x))=>hx.
- have hOn:chi x= 1%R:=characteristic_on_set hChi hx.
  rewrite hOn mule1; split=>hz.
  + left; by split.
  + case:hz=>[[_ hz]|[hn _]]=>//; exfalso; exact:hn hx.
- have hOff:chi x=0%R:=characteristic_off_set hChi hx.
  rewrite hOff mule0; split=>hz.
  + right; split=>//; by symmetry.
  + case:hz=>[[hs _]|[_ hz]]; first by exfalso; exact:hx hs.
    by symmetry.
Qed.
