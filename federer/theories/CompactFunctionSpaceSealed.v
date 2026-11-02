(** Opaque function-space interface for E=K(Y) in Federer (1969), 2.5.20, p.
    114. Only the vector space, evaluations, and proved abstract laws are
    exposed. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra reals topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CompactFunctionSpaceSignature.
(** Source for [space]: the vector space K(Y) of Federer 2.5.20, p. 114. *)
Parameter space : forall (R : realType) (Y : topologicalType), lmodType R.
(** Source for [value]: evaluation of members of K(Y), Federer 2.5.20, p. 114. *)
Parameter value : forall (R : realType) (Y : topologicalType), space R Y -> Y -> R.
(** Source for [laws]: abstract evaluation laws for E=K(Y), Federer 2.5.20, p. 114. *)
Parameter laws : forall (R : realType) (Y : topologicalType), is_compact_function_space (@value R Y).
End CompactFunctionSpaceSignature.
Module CompactFunctionSpace : CompactFunctionSpaceSignature.
(** Source for [space]: private function-space witness for Federer 2.5.20, p. 114. *)
Definition space (R : realType) (Y : topologicalType) := [the lmodType R of CompactFunction R Y].
(** Source for [value]: private evaluation witness for Federer 2.5.20, p. 114. *)
Definition value (R : realType) (Y : topologicalType) : space R Y -> Y -> R := @compact_function_value R Y.
(** Source for [laws]: proved witness laws for E=K(Y), Federer 2.5.20, p. 114. *)
Lemma laws (R : realType) (Y : topologicalType) : is_compact_function_space (@value R Y).
Proof. exact: compact_function_space_witness. Qed.
End CompactFunctionSpace.
