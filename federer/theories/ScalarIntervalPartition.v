(** Public equal interval partitions supporting Federer (1969), 2.10.39,
    printed p. 199. Downstream covering arguments use only the abstract node
    laws. Source context: ScalarIntervalPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarIntervalPartitionUP ScalarIntervalPartitionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [equal_interval_partition]: abstract chosen
    nodes of the equal side subdivision used in
    2.10.39, p. 199. *)
Definition equal_interval_partition (R : realType) (c : R) k
    (hc : 0<=c) (hk : (0<k)%N) := @EqualIntervalPartition.value R c k hc hk.

(** Source for [equal_interval_partition_specification]: proved
    initial, final and equal-step laws for the
    side subdivision used in 2.10.39, p. 199. *)
Theorem equal_interval_partition_specification (R : realType) (c : R) k
    (hc : 0<=c) (hk : (0<k)%N) :
  is_equal_interval_partition c k (@equal_interval_partition R c k hc hk).
Proof. exact: EqualIntervalPartition.laws. Qed.
