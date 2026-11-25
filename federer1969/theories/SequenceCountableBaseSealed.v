(** Federer (1969), 2.2.11, p. 68: sealed witness for the universal
    closed-set construction and its countable-base background. Only the
    abstract laws are exposed; the enumeration or coding witness remains
    private. Source context and the explicit empty-base convention:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace CountableOpenBaseUP SequenceCountableBaseConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SequenceCountableBaseSignature.
(** Source for [value]: abstract witness supporting the universal
    closed-set argument in Federer 2.2.11, p. 68. *)
Parameter value : forall (R : realType), nat -> set (positive_sequence_space R).
(** Source for [laws]: the witness satisfies its specification for
    Federer 2.2.11, p. 68; its construction is not exposed. *)
Parameter laws : forall (R : realType), is_countable_open_base (@value R).
End SequenceCountableBaseSignature.
Module SequenceCountableBase : SequenceCountableBaseSignature.
(** Source for [value]: private selection from proved existence
    for the construction in Federer 2.2.11, p. 68. *)
Definition value (R : realType) := projT1 (cid (sequence_countable_open_base_exists R)).
(** Source for [laws]: the privately selected witness discharges
    the abstract laws for Federer 2.2.11, p. 68. *)
Lemma laws (R : realType) : is_countable_open_base (@value R).
Proof. exact: projT2 (cid (sequence_countable_open_base_exists R)). Qed.
End SequenceCountableBase.
