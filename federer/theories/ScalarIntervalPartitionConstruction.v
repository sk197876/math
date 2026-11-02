(** Private equal-node witness for the interval subdivisions in Federer
    (1969), 2.10.39, printed p. 199. Prove the abstract initial, final and
    equal-step laws; the arithmetic implementation is hidden by opaque
    sealing. Source context: ScalarIntervalPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarIntervalPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [equal_interval_partition_exists]: private
    existence of the equal side subdivision used in
    2.10.39, p. 199. The positive count avoids
    a zero denominator, even for a zero-length side. *)
Theorem equal_interval_partition_exists (R : realType) (c : R) k :
  0<=c -> (0<k)%N -> exists node, is_equal_interval_partition c k node.
Proof.
move=> hc hk; exists (fun i : nat=>i%:R*(c/k%:R)); constructor=> //.
- exact: mul0r.
- by rewrite mulrCA mulfV ?mulr1 // pnatr_eq0 -lt0n.
- move=> i hi; rewrite -addn1 natrD mulrDl mul1r.
  by rewrite addrAC subrr add0r.
Qed.
