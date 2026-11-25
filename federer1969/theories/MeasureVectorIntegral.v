(** Federer (1969), 2.4.12, pp. 87–88: public Banach-valued integral
    characterised by its continuous real dual evaluations. The sealed
    witness proves existence; the previously proved specification laws give
    uniqueness, linearity and the norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP MeasureUP
  MeasureLpMembershipUP MeasureVectorIntegralUP MeasureVectorIntegralSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral]: the vector integral defined in
    Federer 2.4.12, pp. 87–88 The input carries its L1 membership proof, and
    the target's norm and completeness are abstract. *)
Definition measure_vector_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (hf : is_measure_lp_function mu 1%R f) :=
  @MeasureVectorIntegral.value R X V N hN hY mu hm f hf.

(** Source for [measure_vector_integral_specification]: the defining dual
    evaluations of the actual integral in Federer 2.4.12, pp. 87–88
    Downstream results need only this exposed law. *)
Theorem measure_vector_integral_specification (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (hf : is_measure_lp_function mu 1%R f) :
  is_measure_vector_integral mu f (@measure_vector_integral R X V N hN hY mu hm f hf).
Proof. exact: MeasureVectorIntegral.laws. Qed.
