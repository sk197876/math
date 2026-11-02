(** Federer (1969), 3.2.20, p. 257: the compact
    parameter pieces have finite Jacobian integral, justifying the
    finite-multiplicity appeal to 3.2.3, pp. 243–244. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralComparison
  SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_positive_constant_upper_bound]: supporting
    upper comparison in Federer 3.2.20, p. 257, by
    2.4.4(5), p. 82, and 2.4.5, p. 83. No positive
    lower bound on the original partial integrand is imposed. *)
Lemma subset_integral_positive_constant_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u : partial_function X (extended_real_line R)) (a : \bar R) (C : R) :
  measure_measurable mu A -> (0<C)%R ->
  (forall x j,A x -> partial_function_graph u x j -> j<=C%:E) ->
  is_measure_subset_integral mu A u a -> a<=C%:E*mu A.
Proof.
move=> hA hC hBound hI.
pose chi := @CharacteristicFunction.value R X A.
have hChi := @CharacteristicFunction.laws R X A.
pose hi := real_total_integrand (fun x=>(C*chi x)%R).
have hHi : is_measure_integral mu hi (C%:E*mu A) :=
  @measure_positive_characteristic_integral R X mu hm A chi C hChi hA hC.
apply: (@measure_integral_monotone R X mu hm _ hi a _ hI hHi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (measurable_function_domain hI.1))=> x [j hj].
exists j,(C*chi x)%R%:E; split; first exact hj.
split; first by apply/real_total_integrand_graph.
case: (pselect (A x))=> hx.
- have hOn : chi x= 1%R := characteristic_on_set hChi hx.
  rewrite hOn mulr1.
  have hJ := (partial_function_zero_extension_on _ _ _ hx).1 hj.
  exact: (hBound x j hx hJ).
- have hj0 := (partial_function_zero_extension_off _ _ _ hx).1 hj.
  have hOff : chi x=0%R := characteristic_off_set hChi hx.
  by rewrite hj0 hOff mulr0.
Qed.
