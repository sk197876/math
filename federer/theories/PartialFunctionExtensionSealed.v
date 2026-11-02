(** Federer (1969), 2.3.2, p. 73: sealed total extension.
    Source comparison and boundary qualification are documented in
    PartialFunctionExtensionUP.v. This module exports only a witness
    and its graph-preservation specification. *)
From mathcomp Require Import all_boot boolp.
From Federer Require Import PartialFunctionUP PartialFunctionExtensionUP
  PartialFunctionExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PartialFunctionExtensionSignature.
(** Source for [value]: abstract total extension supporting
    Federer 2.3.2, p. 73, with an inhabited target. *)
Parameter value : forall (X Y : Type), partial_function X Y -> Y -> X -> Y.
(** Source for [laws]: graph-preservation specification for the
    extension in Federer 2.3.2, p. 73. *)
Parameter laws : forall (X Y : Type) (f : partial_function X Y) (y0 : Y),
  is_partial_function_total_extension f (@value X Y f y0).
End PartialFunctionExtensionSignature.
Module PartialFunctionExtension : PartialFunctionExtensionSignature.
(** Source for [value]: private witness selection from the proved
    existence of the extension in Federer 2.3.2, p. 73. *)
Definition value (X Y : Type) (f : partial_function X Y) (y0 : Y) :=
  projT1 (cid (@partial_function_total_extension_exists X Y f y0)).
(** Source for [laws]: the selected witness satisfies the abstract
    extension law supporting Federer 2.3.2, p. 73. *)
Lemma laws (X Y : Type) (f : partial_function X Y) (y0 : Y) :
  is_partial_function_total_extension f (@value X Y f y0).
Proof. exact: projT2 (cid (@partial_function_total_extension_exists X Y f y0)). Qed.
End PartialFunctionExtension.
