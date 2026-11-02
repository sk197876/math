(** Public one-dimensional Hausdorff measure for Federer (1969), 2.10.2(1),
    p. 171, and the geometric example in 2.5.10, p. 101. Source context:
    HausdorffLengthUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP
  HausdorffLengthUP HausdorffLengthLaws HausdorffLengthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_length]: the actual m=1
    Hausdorff measure of Federer 2.10.2(1), p. 171. *)
Definition hausdorff_length (R : realType) (X : metricType R) :=
  @HausdorffLength.value R X.

(** Source for [hausdorff_length_specification]: the
    abstract diameter-cover characterization of Federer
    2.10.2(1), p. 171. *)
Lemma hausdorff_length_specification (R : realType) (X : metricType R) :
  is_hausdorff_length (@hausdorff_length R X).
Proof. exact: HausdorffLength.laws. Qed.

(** Source for [hausdorff_length_is_measure]: the measure
    assertion of Federer 2.10.2(1), p. 171. *)
Theorem hausdorff_length_is_measure (R : realType) (X : metricType R) :
  is_measure (@hausdorff_length R X).
Proof. exact: hausdorff_length_measure_law (@hausdorff_length_specification R X). Qed.

(** Source for [hausdorff_length_borel_regular]: Borel regularity in Federer
    2.10.2(1), p. 171 *)
Theorem hausdorff_length_borel_regular (R : realType) (X : metricType R) :
  is_borel_regular_measure (@hausdorff_length R X).
Proof. exact: hausdorff_length_borel_regular_law (@hausdorff_length_specification R X). Qed.
