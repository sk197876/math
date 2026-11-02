(** Sealed small Borel partitions for Federer 2.3.5, p. 76. Source context:
    SmallBorelPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import SmallBorelPartitionUP SmallBorelPartitionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Module Type SmallBorelPartitionSignature.
(** Source for [value]: abstract partition in Federer 2.3.5, p. 76. *)
Parameter value : forall (R : realType) (Y : metricType R) (D : set Y)
  (e : R), countable D -> dense D -> 0 < e -> nat -> set Y.
(** Source for [laws]: the partition laws in Federer 2.3.5, p. 76. *)
Parameter laws : forall (R : realType) (Y : metricType R) (D : set Y)
  (e : R) (hc : countable D) (hd : dense D) (he : 0 < e),
  is_small_borel_partition e (@value R Y D e hc hd he).
End SmallBorelPartitionSignature.
Module SmallBorelPartition : SmallBorelPartitionSignature.
(** Source for [value]: private witness for the partition in
    Federer 2.3.5, p. 76. *)
Definition value (R : realType) (Y : metricType R) (D : set Y)
    (e : R) (hc : countable D) (hd : dense D) (he : 0 < e) :=
  projT1 (cid (@small_borel_partition_exists R Y D e hc hd he)).
(** Source for [laws]: the chosen witness has the partition laws
    required by Federer 2.3.5, p. 76. *)
Lemma laws (R : realType) (Y : metricType R) (D : set Y)
    (e : R) (hc : countable D) (hd : dense D) (he : 0 < e) :
  is_small_borel_partition e (@value R Y D e hc hd he).
Proof. exact: projT2 (cid (@small_borel_partition_exists R Y D e hc hd he)). Qed.
End SmallBorelPartition.
