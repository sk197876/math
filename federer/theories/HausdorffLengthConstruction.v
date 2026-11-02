(** Private existence witness for the one-dimensional Hausdorff measure of
    Federer (1969), 2.10.2(1), p. 171. The already sealed Caratheodory
    measure supplies the witness with the required diameter costs. Source
    context: HausdorffLengthUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameter CaratheodoryMeasure HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_length_exists]: existence of
    the m=1 Hausdorff measure defined in Federer
    2.10.2(1), p. 171. No geometric properties are
    postulated as additional axioms. *)
Theorem hausdorff_length_exists (R : realType) (X : metricType R) :
  exists mu : set X -> \bar R, is_hausdorff_length mu.
Proof.
pose S (j : @nonempty_metric_sets R X) := val j.
pose cost j := extended_metric_diameter (S j).
exists (caratheodory_measure S cost).
exact: caratheodory_measure_specification.
Qed.
