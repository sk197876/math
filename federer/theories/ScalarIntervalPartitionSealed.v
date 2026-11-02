(** Opaque equal interval partitions supporting Federer (1969), 2.10.39,
    printed p. 199. Expose only nodes and their proved abstract laws. Source
    context: ScalarIntervalPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarIntervalPartitionUP ScalarIntervalPartitionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type EQUAL_INTERVAL_PARTITION.
(** Source for [value]: abstract equal side-subdivision
    nodes for 2.10.39, p. 199. *)
Parameter value : forall (R : realType) (c : R) k, 0<=c -> (0<k)%N -> nat -> R.
(** Source for [laws]: abstract equal side-subdivision
    laws for 2.10.39, p. 199. *)
Parameter laws : forall (R : realType) (c : R) k (hc : 0<=c) (hk : (0<k)%N),
  is_equal_interval_partition c k (@value R c k hc hk).
End EQUAL_INTERVAL_PARTITION.
Module EqualIntervalPartition : EQUAL_INTERVAL_PARTITION.
(** Source for [value]: privately proved node witness
    supporting 2.10.39, p. 199, hidden by
    opaque module ascription. *)
Definition value (R : realType) (c : R) k (hc : 0<=c) (hk : (0<k)%N) :=
  projT1 (cid (@equal_interval_partition_exists R c k hc hk)).
(** Source for [laws]: proved equal-node laws supporting
    the side subdivision in 2.10.39, p. 199. *)
Lemma laws (R : realType) (c : R) k (hc : 0<=c) (hk : (0<k)%N) :
  is_equal_interval_partition c k (@value R c k hc hk).
Proof. exact: (projT2 (cid (@equal_interval_partition_exists R c k hc hk))). Qed.
End EqualIntervalPartition.
