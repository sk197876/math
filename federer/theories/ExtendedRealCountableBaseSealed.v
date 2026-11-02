(** General-topology support for Federer (1969), 2.4.17, p. 90 This seal
    exposes a countable base through its laws, hiding rational enumeration. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import CountableOpenBaseUP ExtendedRealOrderTopology ExtendedRealCountableBaseConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ExtendedRealCountableBaseSignature.
(** Source for [value]: abstract countable-base witness supporting
    the continuity assertion of Federer 2.4.17, p. 90. *)
Parameter value : forall R : realType, nat -> set (extended_real_line R).
(** Source for [laws]: countable open base laws for the
    extended exponent line in Federer 2.4.17, p. 90. *)
Parameter laws : forall R : realType, is_countable_open_base (@value R).
End ExtendedRealCountableBaseSignature.
Module ExtendedRealCountableBase : ExtendedRealCountableBaseSignature.
(** Source for [value]: private selection from the proved
    existence of a base supporting Federer 2.4.17, p. 90. *)
Definition value (R : realType) := projT1 (cid (@extended_real_countable_base_exists R)).
(** Source for [laws]: the existence proof supplies the laws
    supporting continuity in Federer 2.4.17, p. 90. *)
Lemma laws (R : realType) : is_countable_open_base (@value R).
Proof. exact: projT2 (cid (@extended_real_countable_base_exists R)). Qed.
End ExtendedRealCountableBase.
