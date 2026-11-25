(** Federer (1969), 4.1.2, p. 348: the
    scalar instance of the original vector integral
    is the original real integral. Its identity
    dual evaluation proves the identification directly. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import TensorUP Hom RealNormUP NormMetric ScalarNormExtendedEmbedding ContinuousRealFunctional
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureVectorIntegralUP
  SummableRealFunctionUP WeakDerivativeFieldVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_vector_integral_identification]: the scalar
    finite Borel sum argument of Federer 4.1.2,
    p. 348, uses the same integral as
    the scalar instance of 2.4.12, p. 87. *)
Theorem scalar_vector_integral_identification (R:realType) (X:choiceType)
    (mu:set X->\bar R) (F:X->R) c:
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(F x:real_norm_metric_space (@scalar_absolute_value_norm R)))) c ->
  is_measure_integral mu (real_total_integrand F) c%:E.
Proof.
move=>hI.
have hId:is_continuous_real_functional (@scalar_absolute_value_norm R) (linear_id R^o).
  exact:(@scalar_norm_real_identity_continuous R).
have h:=hI.2 (linear_id R^o) hId.
apply:(@measure_integral_graph_equivalent R X mu
  (partial_functional_evaluation
    (partial_function_total (fun x=>(F x:real_norm_metric_space (@scalar_absolute_value_norm R))))
    (linear_id R^o)) (real_total_integrand F) c%:E _ h)=>x z.
split.
- move=>[v [hv he]]; apply/real_total_integrand_graph.
  change (F x=v) in hv.
  change (v%:E=z) in he.
  by rewrite hv.
- move/real_total_integrand_graph=>he.
  exists (F x); split; first reflexivity.
  exact he.
Qed.
