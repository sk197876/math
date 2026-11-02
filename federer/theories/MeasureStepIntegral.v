(** Public interface for the step-function assignment in Federer (1969),
    2.4.1, pp. 80–81. Source context and extended-value convention:
    MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureStepFunctionUP MeasureStepIntegralSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measure_step_integral]: public assigned value
    of the step-function sum in Federer 2.4.1, p. 80.
    It is exposed only for functions proved to satisfy the definition. *)
Definition measure_step_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (u : partial_function X (real_line_metric R)) (hu : is_measure_step_function mu u) :=
  @MeasureStepIntegral.value R X mu u hu.

(** Source for [measure_step_integral_specification]: the public
    value satisfies Federer's defining sum, 2.4.1, p. 80. *)
Lemma measure_step_integral_specification (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (u : partial_function X (real_line_metric R)) (hu : is_measure_step_function mu u) :
  is_measure_step_integral mu u (measure_step_integral hu).
Proof. exact: MeasureStepIntegral.laws. Qed.

(** Source for [measure_step_integral_proof_independent]: supporting
    well-definedness of the assignment in Federer 2.4.1, p. 80:
    its value does not depend on the proof that u is a step function. *)
Lemma measure_step_integral_proof_independent (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (u : partial_function X (real_line_metric R)) (hu hv : is_measure_step_function mu u) :
  measure_step_integral hu = measure_step_integral hv.
Proof. exact: measure_step_integral_unique (MeasureStepIntegral.laws hu) (MeasureStepIntegral.laws hv). Qed.
