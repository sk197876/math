(** Federer (1969), 2.10.21, pp. 183–184: continuity of Omega from the
    Hausdorff metric to the cartesian product topology, supporting
    closedness of the convex-set family. Each coordinate changes by at most
    the Hausdorff distance. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSetDistanceProfile HausdorffDistanceUP HausdorffDistance
  CompactHausdorffMetric NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_profile_coordinate_continuous]: supporting
    continuous coordinate of Omega in 2.10.21,
    pp. 183–184, from the defining supremum bound. *)
Lemma hausdorff_profile_coordinate_continuous (R : realType) (X : metricType R) (x : X) :
  continuous (fun C : compact_hausdorff_space X => (compact_set_distance_profile C x : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of compact_hausdorff_space X]
  [the metricType R of real_line_metric R] _ 1 (@ler01 R))=> C D.
rewrite real_line_metric_distanceE compact_hausdorff_distanceE mul1r -opprB normrN.
exact: hausdorff_distance_profile_upper_law (@hausdorff_distance_specification R X) C D x.
Qed.

(** Source for [hausdorff_profile_continuous]: supporting
    continuity of Omega in 2.10.21, pp. 183–184,
    for the product topology of real-valued functions. *)
Theorem hausdorff_profile_continuous (R : realType) (X : metricType R) :
  continuous (fun C : compact_hausdorff_space X =>
    (compact_set_distance_profile C : prod_topology (fun _ : X => real_line_metric R))).
Proof.
move=> C.
pose Q : compact_hausdorff_space X -> prod_topology (fun _ : X => real_line_metric R) :=
  fun D => compact_set_distance_profile D.
pose F := Q @ (nbhs C).
have FF : Filter F by exact: fmap_filter.
change ({ptws, F --> (compact_set_distance_profile C : X -> real_line_metric R)}).
apply: (proj2 (@pointwise_cvgP X [the uniformType of real_line_metric R] F
  (compact_set_distance_profile C) FF))=> x.
exact: (@hausdorff_profile_coordinate_continuous R X x C).
Qed.
