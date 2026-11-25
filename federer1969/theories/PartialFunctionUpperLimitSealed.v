(** Federer (1969), 2.3.2, p. 74: upper limit on the eventual common domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology ExtendedRealBounds
  PartialFunctionLimitExtremaUP PartialFunctionUpperLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type PartialFunctionUpperLimitSignature.
(** Source for [value]: abstract upper limit in Federer 2.3.2, p. 74 *)
Parameter value : forall (R : realType) (X : Type),
  (nat -> partial_function X (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: domain and bound laws for the upper
    limit of Federer 2.3.2, p. 74. *)
Parameter laws : forall (R : realType) (X : Type)
  (f : nat -> partial_function X (extended_real_line R)),
  is_partial_function_upper_limit f (@value R X f).
End PartialFunctionUpperLimitSignature.
Module PartialFunctionUpperLimit : PartialFunctionUpperLimitSignature.
(** Source for [value]: private selection of the proved upper
    limit witness for Federer 2.3.2, p. 74. *)
Definition value (R : realType) (X : Type)
  (f : nat -> partial_function X (extended_real_line R)) :=
  projT1 (cid (@partial_function_upper_limit_exists R X f)).
(** Source for [laws]: the selected witness satisfies the abstract
    upper limit laws for Federer 2.3.2, p. 74. *)
Lemma laws (R : realType) (X : Type)
  (f : nat -> partial_function X (extended_real_line R)) :
  is_partial_function_upper_limit f (@value R X f).
Proof. exact: projT2 (cid (@partial_function_upper_limit_exists R X f)). Qed.
End PartialFunctionUpperLimit.
