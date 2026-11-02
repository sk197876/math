(** Sealed assignment of the numerical sum in Federer (1969), 2.4.1, p. 80.
    Its existence is a proved clause of the step-function predicate. Source
    context and extended-value convention: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureStepFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MeasureStepIntegralSignature.
(** Source for [value]: abstract assigned sum for the step
    function in Federer 2.4.1, p. 80. *)
Parameter value : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (u : partial_function X (real_line_metric R)), is_measure_step_function mu u -> \bar R.
(** Source for [laws]: the assignment satisfies the numerical
    sum specification in Federer 2.4.1, p. 80. *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (u : partial_function X (real_line_metric R)) (hu : is_measure_step_function mu u),
  is_measure_step_integral mu u (@value R X mu u hu).
End MeasureStepIntegralSignature.
Module MeasureStepIntegral : MeasureStepIntegralSignature.
(** Source for [value]: private selection from the existence
    clause of the step-function definition, Federer 2.4.1, p. 80. *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (u : partial_function X (real_line_metric R)) (hu : is_measure_step_function mu u) :=
  projT1 (cid (step_function_sum_defined hu)).
(** Source for [laws]: the selected sum obeys its specification,
    supporting Federer 2.4.1, p. 80. *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (u : partial_function X (real_line_metric R)) (hu : is_measure_step_function mu u) :
  is_measure_step_integral mu u (@value R X mu u hu).
Proof. exact: projT2 (cid (step_function_sum_defined hu)). Qed.
End MeasureStepIntegral.
