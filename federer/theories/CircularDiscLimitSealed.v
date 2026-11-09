(** Opaque original compact-set candidate of Federer (1969),
    3.3.19, p. 302. Compactness and every measure conclusion
    are downstream theorems, not fields of this seal. *)
From mathcomp Require Import all_boot boolp classical_sets reals.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscTreeSealed
  CircularDiscLimitUP CircularDiscLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CircularDiscLimitSignature.
(** Source for [value]: original A of 3.3.19, p. 302. *)
Parameter value:forall R:realType,set (inner_metric_space (@euclidean_inner_productP R 2)).
(** Source for [laws]: exact original level-intersection
    membership of A, 3.3.19, p. 302, independently proved. *)
Parameter laws:forall R:realType,is_circular_disc_limit (@CircularDiscTree.centres R) (@value R).
End CircularDiscLimitSignature.
Module CircularDiscLimit:CircularDiscLimitSignature.
(** Source for [value]: hidden intersection witness for
    the original A in 3.3.19, p. 302. *)
Definition value (R:realType):=projT1 (cid (circular_disc_limit_exists (@CircularDiscTree.centres R))).
(** Source for [laws]: the hidden witness obeys the
    independent intersection law of 3.3.19, p. 302. *)
Lemma laws (R:realType):is_circular_disc_limit (@CircularDiscTree.centres R) (@value R).
Proof. exact:(projT2 (cid (circular_disc_limit_exists (@CircularDiscTree.centres R)))). Qed.
End CircularDiscLimit.
