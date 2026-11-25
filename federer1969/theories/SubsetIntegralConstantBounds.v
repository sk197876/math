(** Federer (1969), 3.2.3, p. 243: integrate the
    two constant Jacobian bounds on each Borel piece.
    This supporting inequality uses the integral order law
    and proved weighted characteristic-function integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP PartialExtendedOrderLoci MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralComparison SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_constant_bounds]: the
    constant-Jacobian integral bounds in Federer 3.2.3,
    p. 243, made explicit for any partial integrand.
    Undefined values on null subsets do not receive defaults;
    the conull integral domain suffices for comparison. *)
Theorem subset_integral_constant_bounds (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X)
    (u:partial_function X (extended_real_line R)) (a : \bar R) (c C:R):
  measure_measurable mu A -> (0<c)%R -> (0<C)%R ->
  (forall x j,A x -> partial_function_graph u x j -> c%:E<=j /\ j<=C%:E) ->
  is_measure_subset_integral mu A u a -> c%:E*mu A<=a /\ a<=C%:E*mu A.
Proof.
move=>hA hc hC hBound hI.
pose chi:=@CharacteristicFunction.value R X A.
have hChi:=@CharacteristicFunction.laws R X A.
pose v:=partial_function_zero_extension (0:extended_real_line R) A u.
pose lo:=real_total_integrand (fun x=>(c*chi x)%R).
pose hi:=real_total_integrand (fun x=>(C*chi x)%R).
have hLo:is_measure_integral mu lo (c%:E*mu A).
  exact (@measure_positive_characteristic_integral R X mu hm A chi c hChi hA hc).
have hHi:is_measure_integral mu hi (C%:E*mu A).
  exact (@measure_positive_characteristic_integral R X mu hm A chi C hChi hA hC).
have hBoth x j:partial_function_graph v x j ->
    (c*chi x)%R%:E<=j /\ j<=(C*chi x)%R%:E.
  move=>hj; case:(pselect (A x))=>hx.
  - have hOn:chi x= 1%R:=characteristic_on_set hChi hx.
    rewrite hOn !mulr1.
    exact (hBound x j hx ((@partial_function_zero_extension_on X (extended_real_line R) 0 A u x j hx).1 hj)).
  - have hOff:chi x=0%R:=characteristic_off_set hChi hx.
    rewrite hOff !mulr0.
    have hz:=(@partial_function_zero_extension_off X (extended_real_line R) 0 A u x j hx).1 hj.
    by rewrite hz; split.
have hDom:=measurable_function_domain hI.1.
split.
- apply:(@measure_integral_monotone R X mu hm lo v _ _ hLo hI).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hDom)=>x [j hj].
  exists (c*chi x)%R%:E,j; split; first by apply/real_total_integrand_graph.
  split; first exact hj; exact (hBoth x j hj).1.
- apply:(@measure_integral_monotone R X mu hm v hi _ _ hI hHi).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hDom)=>x [j hj].
  exists j,(C*chi x)%R%:E; split; first exact hj.
  split; first by apply/real_total_integrand_graph.
  exact (hBoth x j hj).2.
Qed.
