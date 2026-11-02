(** Opaque containing-ball witness for Federer 2.10.19, p. 181 This module
    only seals proved enlargement laws; downstream proofs cannot unfold the
    chosen centres, radii or their case distinction at diameter zero. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffDiameterCost CaratheodoryWeakEnlargementUP
  SphericalEnlargementUP SphericalEnlargementConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SphericalEnlargementSignature.
  (** Source for [value]: sealed containing-generator witness supporting
    Federer 2.10.19, p. 181 *)
  Parameter value : forall (R : realType) (X : metricType R) (m : nat), set X -> set X.
  (** Source for [laws]: abstract weak enlargement laws supporting Federer
    2.10.19, p. 181 *)
  Parameter laws : forall (R : realType) (X : metricType R) (m : nat),
    is_weak_caratheodory_enlargement (@is_positive_metric_closed_ball R X)
      (@hausdorff_diameter_cost R X m) (@value R X m) (spherical_enlargement_control R m).
End SphericalEnlargementSignature.
Module SphericalEnlargement : SphericalEnlargementSignature.
  (** Source for [value]: encapsulated proved containing generator for Federer
    2.10.19, p. 181 *)
  Definition value (R : realType) (X : metricType R) (m : nat) :=
    projT1 (cid (@spherical_enlargement_exists R X m)).
  (** Source for [laws]: proved specification of the sealed enlargement for
    Federer 2.10.19, p. 181 *)
  Lemma laws (R : realType) (X : metricType R) (m : nat) :
    is_weak_caratheodory_enlargement (@is_positive_metric_closed_ball R X)
      (@hausdorff_diameter_cost R X m) (@value R X m) (spherical_enlargement_control R m).
  Proof. exact: projT2 (cid (@spherical_enlargement_exists R X m)). Qed.
End SphericalEnlargement.
