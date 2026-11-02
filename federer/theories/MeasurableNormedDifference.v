(** Federer (1969), 2.3.8, p. 78: differences of members of A(mu,Y), used to
    define their pseudodistance. Source context and domain correction:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric NormMetricSubtractContinuity
  PartialFunctionUP PartialNormedArithmetic MeasureUP MeasurableNormedFunctionUP MeasurableNormedArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [measurable_normed_function_subtract]: direct
    subtractive closure used for the pseudodistance in Federer
    2.3.8, p. 78, including a nonseparable Banach target
    under the defining essential-separability condition. *)
Theorem measurable_normed_function_subtract (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measurable_normed_function mu (partial_vector_subtract f g).
Proof.
move=> hf hg; apply: (@measurable_normed_binary_operation R X V N hN mu hm f g
  (fun p => p.1-p.2) _ _ hf hg).
- exact: real_norm_metric_subtract_continuous.
- move=> Z a z ha hz; exact: subspace_sub ha hz.
Qed.
