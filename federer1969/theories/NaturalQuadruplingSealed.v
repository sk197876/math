(** Opaque interface for the supporting four-digit reindexing used for
    Federer (1969), 2.2.9, p. 65. Only the encoder, decoder and mutually
    inverse laws are public. Source context and attribution:
    NaturalQuadruplingUP.v. *)
From mathcomp Require Import all_boot boolp.
From Federer Require Import NaturalQuadruplingUP NaturalQuadruplingConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type NATURAL_QUADRUPLING.
(** Source for [encode]: supporting quadruple index map for
    the continued-fraction grouping in Federer 2.2.9, p. 65. *)
Parameter encode : (nat * nat) * (nat * nat) -> nat.
(** Source for [decode]: supporting inverse index map for
    the continued-fraction grouping in Federer 2.2.9, p. 65. *)
Parameter decode : nat -> (nat * nat) * (nat * nat).
(** Source for [laws]: supporting inverse-law specification for
    the grouping used with Federer 2.2.9, p. 65. *)
Parameter laws : is_natural_quadrupling encode decode.
End NATURAL_QUADRUPLING.
Module NaturalQuadrupling : NATURAL_QUADRUPLING.
(** Source for [encode]: hidden choice witness for the supporting
    regrouping in Federer 2.2.9, p. 65. *)
Definition encode := projT1 (cid natural_quadrupling_exists).
(** Source for [decode]: hidden inverse choice witness for the
    supporting regrouping in Federer 2.2.9, p. 65. *)
Definition decode := projT1 (cid (projT2 (cid natural_quadrupling_exists))).
(** Source for [laws]: proved specification exposed by the opaque
    regrouping interface supporting Federer 2.2.9, p. 65. *)
Lemma laws : is_natural_quadrupling encode decode.
Proof. exact: projT2 (cid (projT2 (cid natural_quadrupling_exists))). Qed.
End NaturalQuadrupling.
