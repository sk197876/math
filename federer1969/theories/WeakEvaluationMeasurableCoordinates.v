(** Federer (1969), 4.1.1, p. 346: measurable
    fields with values in the weak real dual
    have measurable real evaluations, by the
    weak topology of 2.5.12, p. 103. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground OpenFamilyTopologyUP
  OpenFamilyTopologyMathcomp NormOpenTopology WeakEvaluationTopologyUP ScalarNormExtendedEmbedding
  PartialFunctionBasic MeasureUP MeasurableFunctionUP BorelFunctionBasic MeasurableTotalBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [weak_evaluation_measurable_coordinates]:
    weak measurability implies measurability of
    every evaluation, supporting the distribution
    integral in Federer 4.1.1, p. 346. *)
Theorem weak_evaluation_measurable_coordinates (R:realType) (X E D:choiceType)
    (eval:D->E->R) (O:set (set D)) (hO:is_weak_evaluation_topology eval O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))) ->
  forall y:E,is_measure_measurable_function mu
    (partial_function_total (fun x=>(eval (xi x) y:real_line_metric R))).
Proof.
move=>hXi y.
have hMap:open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R))
  (fun d=>eval d y).
  exact ((hO.2 D O hO.1 id).1 (@open_family_continuous_identity D O) y).
have hNorm:continuous (fun d:open_family_topological_space hO.1=>
  (eval d y:real_norm_metric_space (@scalar_absolute_value_norm R))).
  by rewrite continuousP.
have hReal:continuous (fun d:open_family_topological_space hO.1=>(eval d y:real_line_metric R)).
  move=>d; exact:(continuous_comp (hNorm d) (@ScalarNormExtendedEmbedding.scalar_norm_real_identity_continuous R _)).
exact:(measurable_total_borel_postcomposition hm hXi (continuous_borel_function hReal)).
Qed.
