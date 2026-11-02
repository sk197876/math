(** Federer (1969), 2.2.11, p. 68: sealed witness for the universal
    closed-set construction and its countable-base background. Only the
    abstract laws are exposed; the enumeration or coding witness remains
    private. Source context and the explicit empty-base convention:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace CountableOpenBaseUP UniversalClosedSetUP UniversalClosedConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type UniversalClosedSetSignature.
(** Source for [value]: abstract witness supporting the universal
    closed-set argument in Federer 2.2.11, p. 68. *)
Parameter value : forall (R : realType) (T : topologicalType) (U : nat -> set T)
    (hU : is_countable_open_base U), set (T * positive_sequence_space R).
(** Source for [laws]: the witness satisfies its specification for
    Federer 2.2.11, p. 68; its construction is not exposed. *)
Parameter laws : forall (R : realType) (T : topologicalType) (U : nat -> set T)
    (hU : is_countable_open_base U), is_universal_closed_set (@value R T U hU).
End UniversalClosedSetSignature.
Module UniversalClosedSet : UniversalClosedSetSignature.
(** Source for [value]: private selection from proved existence
    for the construction in Federer 2.2.11, p. 68. *)
Definition value (R : realType) (T : topologicalType) (U : nat -> set T)
    (hU : is_countable_open_base U) := projT1 (cid (@universal_closed_set_exists R T U hU)).
(** Source for [laws]: the privately selected witness discharges
    the abstract laws for Federer 2.2.11, p. 68. *)
Lemma laws (R : realType) (T : topologicalType) (U : nat -> set T)
    (hU : is_countable_open_base U) : is_universal_closed_set (@value R T U hU).
Proof. exact: projT2 (cid (@universal_closed_set_exists R T U hU)). Qed.
End UniversalClosedSet.
