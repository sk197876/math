(** Sealed finite difference partitions supporting Federer
    (1969), 2.8.20, p. 152. The explicit nine-cell
    grid is private; later packing uses only the finite,
    rectangular, disjoint and union laws. Source titles and
    comparisons: HalfOpenRectangleDifferenceConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals.
From Federer Require Import ScalarHalfOpenRectangles FiniteHalfOpenPartitionUP
  HalfOpenRectangleDifferenceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type HalfOpenRectangleDifferenceSignature.
(** Source for [value]: abstract difference partition
    supporting Federer 2.8.20, p. 152. *)
Parameter value : forall (R : realType) (A B : set (R*R)),
  is_nondegenerate_half_open_rectangle A -> is_nondegenerate_half_open_rectangle B ->
  set (set (R*R)).
(** Source for [laws]: the selected difference family obeys
    the proved specification supporting Federer 2.8.20,
    p. 152; FiniteHalfOpenPartitionUP.v. *)
Parameter laws : forall (R : realType) (A B : set (R*R))
  (hA : is_nondegenerate_half_open_rectangle A) (hB : is_nondegenerate_half_open_rectangle B),
  is_finite_half_open_partition (A `\` B) (@value R A B hA hB).
End HalfOpenRectangleDifferenceSignature.
Module HalfOpenRectangleDifference : HalfOpenRectangleDifferenceSignature.
(** Source for [value]: opaque selection from the proved
    difference partition supporting Federer 2.8.20, p. 152. *)
Definition value (R : realType) (A B : set (R*R))
    (hA : is_nondegenerate_half_open_rectangle A) (hB : is_nondegenerate_half_open_rectangle B) :=
  projT1 (cid (@half_open_rectangle_difference_partition_exists R A B hA hB)).
(** Source for [laws]: the selected witness has the abstract
    laws supporting Federer 2.8.20, p. 152. *)
Lemma laws (R : realType) (A B : set (R*R))
    (hA : is_nondegenerate_half_open_rectangle A) (hB : is_nondegenerate_half_open_rectangle B) :
  is_finite_half_open_partition (A `\` B) (@value R A B hA hB).
Proof. exact: projT2 (cid (@half_open_rectangle_difference_partition_exists R A B hA hB)). Qed.
End HalfOpenRectangleDifference.
