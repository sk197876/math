(** Federer (1969), 2.2.10(2), p. 67: sealed partition A(s) associated with
    the closed-cover tree E. Only the root and recursive laws are exposed.
    Source context and word convention: CoverPartitionTreeUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import CoverPartitionTreeUP CoverPartitionTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CoverPartitionTreeSignature.
(** Source for [value]: abstract partition witness A(s) for
    Federer 2.2.10(2), p. 67. *)
Parameter value : forall T : Type, (seq nat -> set T) -> seq nat -> set T.
(** Source for [laws]: the witness satisfies the defining
    equations printed in Federer 2.2.10(2), p. 67. *)
Parameter laws : forall (T : Type) (E : seq nat -> set T),
  is_cover_partition_tree E (@value T E).
End CoverPartitionTreeSignature.
Module CoverPartitionTree : CoverPartitionTreeSignature.
(** Source for [value]: private selection from the proved
    existence construction for Federer 2.2.10(2), p. 67. *)
Definition value (T : Type) (E : seq nat -> set T) := projT1 (cid (cover_partition_tree_exists E)).
(** Source for [laws]: the selected witness satisfies the
    abstract equations of Federer 2.2.10(2), p. 67. *)
Lemma laws (T : Type) (E : seq nat -> set T) : is_cover_partition_tree E (@value T E).
Proof. exact: projT2 (cid (cover_partition_tree_exists E)). Qed.
End CoverPartitionTree.
