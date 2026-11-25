(** Federer (1969), 2.4.14, p. 88: real-valued functions in the signed
    product integral. This supporting topology adapter identifies the scalar
    norm metric with the real-line metric and embeds finite values into the
    extended-real integration interface. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground
  ExtendedRealOrderTopology MeasurableRealEmbedding PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_norm_real_identity_continuous]: supporting
    metric identification for the real scalar Lp spaces in
    Federer 2.4.14, p. 88. The identity preserves
    absolute-difference distance exactly. *)
Lemma scalar_norm_real_identity_continuous (R : realType) :
  continuous (fun x : real_norm_metric_space (scalar_absolute_value_norm R) => (x : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=> x y.
change (`|x-y| <= 1 * `|x-y|); by rewrite mul1r.
Qed.

(** Source for [scalar_norm_extended_embedding_continuous]: the
    finite scalar inclusion supporting the integral in Federer
    2.4.14, p. 88. This is topology infrastructure,
    not an additional numbered claim. *)
Lemma scalar_norm_extended_embedding_continuous (R : realType) :
  continuous (fun x : real_norm_metric_space (scalar_absolute_value_norm R) => (x%:E : extended_real_line R)).
Proof.
move=> x; exact (@continuous_comp
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
  [the topologicalType of real_line_metric R] (extended_real_line R)
  (fun y => (y : real_line_metric R)) (fun y => (y%:E : extended_real_line R)) x
  (@scalar_norm_real_identity_continuous R x) (@real_extended_embedding_continuous R x)).
Qed.

(** Source for [partial_scalar_extended_embedding]: supporting
    finite inclusion for the real functions in Federer 2.4.14,
    p. 88. Postcomposition keeps the original partial domain. *)
Definition partial_scalar_extended_embedding (R : realType) (X : Type)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  partial_function_postcompose f (fun x => (x%:E : extended_real_line R)).

(** Source for [measurable_scalar_extended_embedding]: supporting
    measurability of the real integrands in Federer 2.4.14,
    p. 88, under the finite scalar inclusion. *)
Lemma measurable_scalar_extended_embedding (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_scalar_extended_embedding f).
Proof.
move=> hf; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm _ _ hf).
apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
Qed.
