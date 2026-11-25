(** Federer (1969), 2.10.21, p. 183: the family of nonempty compact subsets
    with the Hausdorff metric. This adapter uses only the sealed distance
    laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot reals topology.
From Federer Require Import CompactSetDistanceProfile HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [compact_hausdorff_space]: direct metric
    carrier F of 2.10.21, p. 183. A type
    alias separates its Hausdorff topology from the
    raw choice-type carrier used in the specification. *)
Definition compact_hausdorff_space (R : realType) (X : metricType R) : Type := compact_metric_set X.
HB.instance Definition _ (R : realType) (X : metricType R) :=
  Choice.copy (compact_hausdorff_space X) (compact_metric_set X).
Section Metric.
Variable R : realType.
Variable X : metricType R.
Local Notation H := (compact_hausdorff_space X).
HB.instance Definition _ := isMetric.Build R H
  (hausdorff_distance_self_law (@hausdorff_distance_specification R X))
  (hausdorff_distance_separates_law (@hausdorff_distance_specification R X))
  (hausdorff_distance_symmetric_law (@hausdorff_distance_specification R X))
  (hausdorff_distance_triangle_law (@hausdorff_distance_specification R X)).

(** Source for [compact_hausdorff_distanceE]: metric
    compatibility of F with the distance specified
    in 2.10.21, p. 183. *)
Lemma compact_hausdorff_distanceE (C D : H) : mdist C D=hausdorff_distance C D.
Proof. by []. Qed.
End Metric.
