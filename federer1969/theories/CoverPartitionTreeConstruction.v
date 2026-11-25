(** Federer (1969), 2.2.10(2), p. 67: private construction of the Borel
    partition A(s) by the printed recursion. The implementation is hidden;
    later arguments use only the specified recursion laws. Source context:
    CoverPartitionTreeUP.v. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import SetSequenceDisjointification CoverPartitionTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [cover_partition_recursion]: private witness for
    the recursive formula A(s) in Federer 2.2.10(2), p. 67,
    with the last coordinate at the head of the stored word. *)
Fixpoint cover_partition_recursion (T : Type) (E : seq nat -> set T) (s : seq nat) : set T :=
  if s is j::t then cover_partition_recursion E t `&`
    set_sequence_disjointify (fun i => E (i::t)) j else setT.

(** Source for [cover_partition_tree_exists]: supporting existence
    of the specified partition in Federer 2.2.10(2), p. 67.
    Its Borel and partition properties follow separately from the
    closed-cover laws, rather than being assumed of the witness. *)
Theorem cover_partition_tree_exists (T : Type) (E : seq nat -> set T) :
  exists A, is_cover_partition_tree E A.
Proof. exists (cover_partition_recursion E); by constructor. Qed.
