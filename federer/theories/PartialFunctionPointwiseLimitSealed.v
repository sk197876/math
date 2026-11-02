(** Opaque pointwise-limit interface for Federer (1969), 2.3.9, pp. 79–80.
    Source context and partial-domain convention:
    PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot boolp reals topology.
From Federer Require Import PartialFunctionUP PartialFunctionPointwiseLimitUP
  PartialFunctionPointwiseLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PartialFunctionPointwiseLimitSignature.
(** Source for [value]: abstract pointwise-limit function in
    Federer 2.3.9, pp. 79–80. *)
Parameter value : forall (R : realType) (X : Type) (Y : metricType R),
  (nat -> partial_function X Y) -> partial_function X Y.
(** Source for [laws]: proved graph specification for h in
    Federer 2.3.9, pp. 79–80. *)
Parameter laws : forall (R : realType) (X : Type) (Y : metricType R)
  (f : nat -> partial_function X Y),
  is_partial_function_pointwise_limit f (@value R X Y f).
End PartialFunctionPointwiseLimitSignature.
Module PartialFunctionPointwiseLimit : PartialFunctionPointwiseLimitSignature.
(** Source for [value]: private witness selection for the
    pointwise limit in Federer 2.3.9, pp. 79–80. *)
Definition value (R : realType) (X : Type) (Y : metricType R)
    (f : nat -> partial_function X Y) :=
  projT1 (cid (@partial_function_pointwise_limit_exists R X Y f)).
(** Source for [laws]: the selected function obeys the abstract
    graph law supporting Federer 2.3.9, pp. 79–80. *)
Lemma laws (R : realType) (X : Type) (Y : metricType R)
    (f : nat -> partial_function X Y) :
  is_partial_function_pointwise_limit f (@value R X Y f).
Proof. exact: projT2 (cid (@partial_function_pointwise_limit_exists R X Y f)). Qed.
End PartialFunctionPointwiseLimit.
