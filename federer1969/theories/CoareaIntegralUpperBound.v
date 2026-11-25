(** Federer (1969), 3.2.11, p. 249: integrate
    the uniform upper bound for the perturbed Jacobian.
    This supporting measure lemma uses the integral comparison
    law and the existing opaque characteristic function. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  PartialExtendedOrderLoci MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralComparison
  SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_subset_integral_upper_constant]:
    the first inequality in the critical-rank proof of
    Federer 3.2.11, p. 249. Supporting upper-bound
    version of the characteristic comparison used in 3.2.3:
    an actual subset integral is at most C times source
    mass when its existing values on the subset are at
    most C. No positive lower bound for the integrand is required. *)
Theorem coarea_subset_integral_upper_constant (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X)
    (u:partial_function X (extended_real_line R)) a (C:R):
  measure_measurable mu A ->(0<C)%R ->
  (forall x j,A x ->partial_function_graph u x j ->j<=C%:E) ->
  is_measure_subset_integral mu A u a ->a<=C%:E*mu A.
Proof.
move=>hA hC hBound hI.
pose chi:=@CharacteristicFunction.value R X A.
have hChi:=@CharacteristicFunction.laws R X A.
pose v:=partial_function_zero_extension (0:extended_real_line R) A u.
pose hi:=real_total_integrand (fun x=>(C*chi x)%R).
have hHi:is_measure_integral mu hi (C%:E*mu A).
  exact (@measure_positive_characteristic_integral R X mu hm A chi C hChi hA hC).
have hPoint x j:partial_function_graph v x j ->j<=(C*chi x)%R%:E.
  move=>hj; case:(pselect (A x))=>hx.
  - have hOn:chi x= 1%R:=characteristic_on_set hChi hx.
    rewrite hOn mulr1.
    exact (hBound x j hx ((@partial_function_zero_extension_on X (extended_real_line R) 0 A u x j hx).1 hj)).
  - have hOff:chi x= 0%R:=characteristic_off_set hChi hx.
    rewrite hOff mulr0.
    have hz:=(@partial_function_zero_extension_off X (extended_real_line R) 0 A u x j hx).1 hj.
    by rewrite hz.
apply:(@measure_integral_monotone R X mu hm v hi _ _ hI hHi).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hI.1))=>x [j hj].
exists j,(C*chi x)%R%:E; split; first exact hj.
split; first by apply/real_total_integrand_graph.
exact (hPoint x j hj).
Qed.
