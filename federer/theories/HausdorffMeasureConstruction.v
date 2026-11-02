(** Private integer-degree existence witnesses for Federer (1969),
    2.10.2(1)–(2), p. 171. Apply the already sealed abstract Caratheodory
    construction separately to each generator family. Their eventual
    equality and geometric comparisons are not assumed by these witnesses.
    Source context and radius conventions: HausdorffMeasureUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffLengthUP HausdorffDiameterCost CaratheodoryMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [hausdorff_measure_exists]: existence of
    integer-dimensional Hausdorff measure as defined in Federer
    2.10.2(1), p. 171, from the proved construction 2.10.1. *)
Theorem hausdorff_measure_exists (R : realType) (X : metricType R) (m : nat) :
  exists mu : set X -> \bar R, is_hausdorff_measure m mu.
Proof.
exists (@caratheodory_measure R X (@nonempty_metric_sets R X)
  (fun A => val A) (fun A => hausdorff_diameter_cost m (val A))).
exact: caratheodory_measure_specification.
Qed.

(** Source for [closed_hausdorff_measure_exists]: independent
    existence of the closed-cover variant in Federer
    2.10.2(1), p. 171; equality is proved separately. *)
Theorem closed_hausdorff_measure_exists (R : realType) (X : metricType R) (m : nat) :
  exists mu : set X -> \bar R, is_closed_hausdorff_measure m mu.
Proof.
exists (@caratheodory_measure R X (@nonempty_closed_metric_sets R X)
  (fun A => val A) (fun A => hausdorff_diameter_cost m (val A))).
exact: caratheodory_measure_specification.
Qed.

(** Source for [open_hausdorff_measure_exists]: independent
    existence of the open-cover variant in Federer
    2.10.2(1), p. 171, without identifying its approximations
    with the unrestricted ones. *)
Theorem open_hausdorff_measure_exists (R : realType) (X : metricType R) (m : nat) :
  exists mu : set X -> \bar R, is_open_hausdorff_measure m mu.
Proof.
exists (@caratheodory_measure R X (@nonempty_open_metric_sets R X)
  (fun A => val A) (fun A => hausdorff_diameter_cost m (val A))).
exact: caratheodory_measure_specification.
Qed.

(** Source for [spherical_measure_exists]: existence of the
    integer-dimensional spherical measure of Federer
    2.10.2(2), p. 171, using the strictly positive real
    radius convention of the referenced 2.8.1, p. 141. *)
Theorem spherical_measure_exists (R : realType) (X : metricType R) (m : nat) :
  exists mu : set X -> \bar R, is_spherical_measure m mu.
Proof.
exists (@caratheodory_measure R X (@positive_closed_metric_balls R X)
  (fun A => val A) (fun A => hausdorff_diameter_cost m (val A))).
exact: caratheodory_measure_specification.
Qed.
