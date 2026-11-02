(** Federer (1969), 2.10.21, p. 183: seal the proved Hausdorff-distance
    witness. Only its supremum laws are exposed. *)
From mathcomp Require Import all_boot boolp reals topology.
From Federer Require Import CompactSetDistanceProfile HausdorffDistanceUP HausdorffDistanceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HausdorffDistanceSignature.
(** Source for [value]: abstract distance of 2.10.21,
    p. 183, on nonempty compact subsets. *)
Parameter value : forall (R : realType) (X : metricType R),
  compact_metric_set X -> compact_metric_set X -> R.
(** Source for [laws]: supremum laws of 2.10.21,
    p. 183, independent of the maximum witnesses. *)
Parameter laws : forall (R : realType) (X : metricType R), is_hausdorff_distance (@value R X).
End HausdorffDistanceSignature.
Module HausdorffDistance : HausdorffDistanceSignature.
(** Source for [value]: private selection of the proved
    distance witness for 2.10.21, p. 183. *)
Definition value (R : realType) (X : metricType R) :=
  projT1 (cid (@hausdorff_distance_exists R X)).
(** Source for [laws]: the selected witness satisfies
    the defining supremum laws of 2.10.21, p. 183. *)
Lemma laws (R : realType) (X : metricType R) : is_hausdorff_distance (@value R X).
Proof. exact: projT2 (cid (@hausdorff_distance_exists R X)). Qed.
End HausdorffDistance.
