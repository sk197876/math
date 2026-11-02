(** Federer (1969), 2.4.12, p. 87: scalar evaluations alpha o f used to
    define the vector integral. This supporting step establishes
    measurability. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasurableFunctionUP MeasurablePostcomposition MeasurableRealEmbedding BorelFunctionBasic
  ContinuousRealFunctional MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_functional_evaluation]: supporting measurability
    of alpha o f in Federer 2.4.12, p. 87 The map keeps the exact original
    domain and embeds finite scalar values into the extended line. *)
Lemma measurable_functional_evaluation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (a : {linear V -> R^o}) :
  is_measure_measurable_function mu f -> is_continuous_real_functional hN a ->
  is_measure_measurable_function mu (partial_functional_evaluation f a).
Proof.
move=> hf ha; apply: (@measurable_function_borel_postcomposition R X
  [the topologicalType of real_norm_metric_space hN] (extended_real_line R) mu hm f _ hf).
apply: continuous_borel_function=> x.
exact: (continuous_comp (ha x) (@real_extended_embedding_continuous R (a x))).
Qed.
