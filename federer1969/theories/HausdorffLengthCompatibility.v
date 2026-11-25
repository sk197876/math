(** Degree-one compatibility for Federer (1969), 2.10.2(1), p. 171: the
    normalized integer-degree family agrees with the Hausdorff length
    already used for 2.5.10, p. 101. Source context and normalization
    conventions: HausdorffDiameterCost.v and HausdorffLengthUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffMeasureLaws
  HausdorffLengthUP HausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [hausdorff_measure_one_length]: supporting
    exact agreement with Hausdorff length in Federer
    2.10.2(1), p. 171. Uniqueness compares two
    independently sealed witnesses through their laws. *)
Theorem hausdorff_measure_one_length (R : realType) (X : metricType R) (A : set X) :
  @hausdorff_measure R X 1 A=@hausdorff_length R X A.
Proof.
exact (@hausdorff_length_unique R X _ _
  ((@hausdorff_one_degree_length_specification R X _).1 (@hausdorff_measure_specification R X 1))
  (@hausdorff_length_specification R X) A).
Qed.
