(** Federer (1969), 2.10.39, printed p. 199: subdivide each of the longer
    box sides into equal intervals. Specify the finite node laws
    independently of a construction. Only nodes numbered from zero through
    the chosen count are constrained; later node values are irrelevant. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_equal_interval_partition]: supporting
    specification of an equal finite subdivision of a
    box side in 2.10.39, p. 199.
    The count is explicitly positive; a zero side
    length is allowed without a zero denominator. *)
Record is_equal_interval_partition (R : realType) (c : R) (k : nat)
    (node : nat -> R) : Prop := {
  (** Source for [equal_interval_count_positive_law]: supporting
      positive subdivision counts in 2.10.39, p. 199. *)
  equal_interval_count_positive_law : (0<k)%N;
  (** Source for [equal_interval_length_nonnegative_law]: supporting
      nonnegative side lengths for the subdivision in
      2.10.39, p. 199, including degenerate sides. *)
  equal_interval_length_nonnegative_law : 0<=c;
  (** Source for [equal_interval_initial_law]: supporting
      first endpoint of the subdivision in 2.10.39,
      p. 199, after translating the side to zero. *)
  equal_interval_initial_law : node 0=0;
  (** Source for [equal_interval_final_law]: supporting
      final endpoint of the subdivided box side in
      2.10.39, p. 199. *)
  equal_interval_final_law : node k=c;
  (** Source for [equal_interval_step_law]: supporting
      equal side lengths c_i/k_i of the small
      boxes in 2.10.39, p. 199. *)
  equal_interval_step_law : forall i, (i<k)%N -> node i.+1-node i=c/k%:R
}.
