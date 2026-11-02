(** Federer (1969), 2.4.12, p. 86: the finite-p norm formula exposed through
    its abstract integral-root laws. Source context and conventions:
    MeasureLpNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureLpNormUP MeasureLpNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type MeasureLpNormSignature.
(** Source for [value]: the finite-p value of Federer 2.4.12,
    p. 86, hidden behind its integral-root specification. *)
Parameter value : forall (R : realType) (X : choiceType) (Y : Type),
  (set X -> \bar R) -> (Y -> R) -> R -> partial_function X Y -> \bar R.
(** Source for [laws]: abstract characterisation of the value
    in Federer 2.4.12, p. 86, for measurable normed functions. *)
Parameter laws : forall (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)),
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  is_measure_lp_norm mu N p f (@value R X (real_norm_metric_space hN) mu N p f).
End MeasureLpNormSignature.
Module MeasureLpNorm : MeasureLpNormSignature.
(** Source for [value]: private witness for the finite-p
    value of Federer 2.4.12, p. 86. *)
Definition value := @measure_lp_norm_witness.
(** Source for [laws]: the private witness proves the public
    specification of Federer 2.4.12, p. 86. *)
Lemma laws (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)) :
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  is_measure_lp_norm mu N p f (@value R X (real_norm_metric_space hN) mu N p f).
Proof. move=> hm hp hf; exact (@measure_lp_norm_witness_laws R X V N hN mu hm p f hp hf). Qed.
End MeasureLpNorm.
