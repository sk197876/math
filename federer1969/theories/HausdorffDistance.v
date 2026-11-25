(** Federer (1969), 2.10.21, p. 183: public Hausdorff distance through its
    sealed supremum laws. *)
From mathcomp Require Import all_boot reals topology.
From Federer Require Import CompactSetDistanceProfile HausdorffDistanceUP HausdorffDistanceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [hausdorff_distance]: direct distance
    of 2.10.21, p. 183, without exposing its
    compact-maximum existence witnesses. *)
Definition hausdorff_distance (R : realType) (X : metricType R) := @HausdorffDistance.value R X.

(** Source for [hausdorff_distance_specification]: direct
    supremum specification in 2.10.21, p. 183. *)
Lemma hausdorff_distance_specification (R : realType) (X : metricType R) :
  is_hausdorff_distance (@hausdorff_distance R X).
Proof. exact: HausdorffDistance.laws. Qed.
