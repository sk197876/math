(** Federer (1969), 2.2.9, p. 65: sealed real interval tree. Only its
    abstract laws, including countable loss at every stage, are exposed; the
    grid and recursive endpoint choices remain private. Source context:
    RealIntervalTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground RealIntervalTreeUP RealIntervalTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type RealIntervalTreeSignature.
(** Source for [value]: supporting real interval tree for the
    countable-complement assertion in Federer 2.2.9, p. 65. *)
Parameter value : forall R : realType, seq nat -> set (real_line_metric R).
(** Source for [laws]: the abstract interval and countable-loss
    laws required by Federer 2.2.9, p. 65. *)
Parameter laws : forall R : realType, is_real_interval_embedding_tree (@value R).
End RealIntervalTreeSignature.
Module RealIntervalTree : RealIntervalTreeSignature.
(** Source for [value]: private witness selection from the
    proved real interval-tree existence in Federer 2.2.9, p. 65. *)
Definition value (R : realType) := projT1 (cid (@real_interval_embedding_tree_exists R)).
(** Source for [laws]: the selected real interval tree satisfies
    its abstract specification, supporting Federer 2.2.9, p. 65. *)
Lemma laws (R : realType) : is_real_interval_embedding_tree (@value R).
Proof. exact: projT2 (cid (@real_interval_embedding_tree_exists R)). Qed.
End RealIntervalTree.
