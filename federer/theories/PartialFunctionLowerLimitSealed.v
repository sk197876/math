(** Federer (1969), 2.3.2, p. 74: lower limit on the eventual common domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology ExtendedRealBounds
  PartialFunctionLimitExtremaUP PartialFunctionLowerLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type PartialFunctionLowerLimitSignature.
(** Source for [value]: abstract lower limit in Federer 2.3.2, p. 74 *)
Parameter value : forall (R : realType) (X : Type),
  (nat -> partial_function X (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: domain and bound laws for the lower
    limit of Federer 2.3.2, p. 74. *)
Parameter laws : forall (R : realType) (X : Type)
  (f : nat -> partial_function X (extended_real_line R)),
  is_partial_function_lower_limit f (@value R X f).
End PartialFunctionLowerLimitSignature.
Module PartialFunctionLowerLimit : PartialFunctionLowerLimitSignature.
(** Source for [value]: private selection of the proved lower
    limit witness for Federer 2.3.2, p. 74. *)
Definition value (R : realType) (X : Type)
  (f : nat -> partial_function X (extended_real_line R)) :=
  projT1 (cid (@partial_function_lower_limit_exists R X f)).
(** Source for [laws]: the selected witness satisfies the abstract
    lower limit laws for Federer 2.3.2, p. 74. *)
Lemma laws (R : realType) (X : Type)
  (f : nat -> partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f (@value R X f).
Proof. exact: projT2 (cid (@partial_function_lower_limit_exists R X f)). Qed.
End PartialFunctionLowerLimit.
