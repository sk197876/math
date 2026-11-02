(** Opaque interface for the zero extension of Federer (1969), 2.4.10, p.
    85. Source context and abstract graph specification:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import PartialFunctionUP PartialZeroExtensionUP PartialZeroExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type PartialZeroExtensionSignature.
(** Source for [value]: f_A of Federer 2.4.10,
    p. 85, exposed only through its defining laws. *)
Parameter value : forall (X Y : Type), Y -> set X -> partial_function X Y -> partial_function X Y.
(** Source for [laws]: graph laws defining f_A in
    Federer 2.4.10, p. 85. *)
Parameter laws : forall (X Y : Type) (zero : Y) (A : set X) (f : partial_function X Y),
  is_partial_function_zero_extension zero A f (@value X Y zero A f).
End PartialZeroExtensionSignature.
Module PartialZeroExtension : PartialZeroExtensionSignature.
(** Source for [value]: private selection of the proved
    zero-extension witness for Federer 2.4.10, p. 85. *)
Definition value (X Y : Type) (zero : Y) (A : set X) (f : partial_function X Y) :=
  projT1 (cid (partial_zero_extension_exists zero A f)).
(** Source for [laws]: witness satisfies the abstract
    zero-extension laws of Federer 2.4.10, p. 85. *)
Lemma laws (X Y : Type) (zero : Y) (A : set X) (f : partial_function X Y) :
  is_partial_function_zero_extension zero A f (@value X Y zero A f).
Proof. exact: projT2 (cid (partial_zero_extension_exists zero A f)). Qed.
End PartialZeroExtension.
