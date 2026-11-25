(** Federer (1969), 4.1.5, pp. 349–350:
    the normalized weak dual density has finite norm
    integral on every original compact set. Radon
    compact finiteness and the proved everywhere
    unit-ball representative supply the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses VectorDaniellNormalisationUP
  WeakDualFunctionalNorm PartialFunctionBasic PartialZeroExtension MeasureUP RadonMeasureUP RadonBorelRegularity
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  MeasureSubsetIntegral UnitBoundedSubsetIntegralFinite ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalised_weak_density_compact_norm_integral]:
    the original compact local norm integrability
    required in Federer 4.1.5, p. 349, for
    the normalized representative constructed on p. 350.
    It needs no positive total-mass premise. *)
Theorem normalised_weak_density_compact_norm_integral
    (R:realType) (X:topologicalType) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (Q:set (X->Y)) (T:(X->Y)->R) (k:X->weak_dual_space hNY):
  is_normalised_vector_daniell_density mu Q T k ->
  forall K:set X,compact K ->exists c:R,
    is_measure_subset_integral mu K (real_total_integrand (fun x=>dual_norm NY (val (k x)))) c%:E /\
    0<=c /\ (c%:E<=mu K)%E.
Proof.
move=>hk K hK.
have hNormMeasurable:=normalised_vector_density_norm_measurable hk.
have hTotal:is_measure_measurable_function mu
    (partial_function_total (fun x:X=>((dual_norm NY (val (k x)))%:E:extended_real_line R))).
  apply:(@measurable_function_graph_equivalent R X (extended_real_line R) mu
    (real_total_integrand (fun x=>dual_norm NY (val (k x)))) _ _ hNormMeasurable)=>x y.
  exact:real_total_integrand_graph.
have hBounds:forall x,
    ((0:extended_real_line R)<=(dual_norm NY (val (k x)))%:E<= 1)%E.
  move=>x; apply/andP; split.
  - change (is_true (0%:E<=(dual_norm NY (val (k x)))%:E)%E).
    rewrite lee_fin; exact:(@weak_dual_functional_norm_nonnegative R Y NY hNY (k x)).
  - change (is_true ((dual_norm NY (val (k x)))%:E<=1%:E)%E).
    rewrite lee_fin; exact:normalised_vector_density_bound hk x.
have[c [hI [hc hUpper]]]:=@unit_bounded_nonnegative_subset_integral_finite R X mu hm K
  (fun x=>(dual_norm NY (val (k x)))%:E)
  (radon_compact_measurable hm hr hK) (radon_compact_finite hr hK) hTotal hBounds.
exists c; split; last by split.
apply:(@measure_integral_graph_equivalent R X mu _ _ c%:E _ hI)=>x y.
case:(pselect (K x))=>hx.
- by rewrite !partial_function_zero_extension_on // real_total_integrand_graph.
- by rewrite !partial_function_zero_extension_off.
Qed.
