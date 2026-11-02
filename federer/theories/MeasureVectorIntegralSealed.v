(** Federer (1969), 2.4.12, pp. 87–88: sealed integral on all L1 functions
    with a complete normed target. Only the abstract dual-evaluation
    specification is exposed; the approximation and limiting witness are
    hidden. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP MeasureUP MeasureStepFunctionUP
  MeasureLpMembershipUP MeasureVectorIntegralUP MeasureVectorIntegralConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.
Module Type MeasureVectorIntegralSignature.
(** Source for [value]: abstract Banach-valued integral used in Federer
    2.4.12, pp. 87–88 *)
Parameter value : forall (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN)),
  is_measure_lp_function mu 1%R f -> V.
(** Source for [laws]: the selected vector satisfies Federer's
    integral specification, 2.4.12, pp. 87–88. *)
Parameter laws : forall (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN))
  (hf : is_measure_lp_function mu 1%R f),
  is_measure_vector_integral mu f (@value R X V N hN hY mu hm f hf).
End MeasureVectorIntegralSignature.
Module MeasureVectorIntegral : MeasureVectorIntegralSignature.
(** Source for [value]: private selection of a proved integral
    witness for Federer 2.4.12, pp. 87–88. *)
Definition value (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN))
  (hf : is_measure_lp_function mu 1%R f) :=
  projT1 (cid (@measure_vector_integral_exists R X V N hN hY mu hm f hf)).
(** Source for [laws]: the witness proves the exposed dual
    specification supporting Federer 2.4.12, pp. 87–88. *)
Lemma laws (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN))
  (hf : is_measure_lp_function mu 1%R f) :
  is_measure_vector_integral mu f (@value R X V N hN hY mu hm f hf).
Proof. exact: projT2 (cid (@measure_vector_integral_exists R X V N hN hY mu hm f hf)). Qed.
End MeasureVectorIntegral.
