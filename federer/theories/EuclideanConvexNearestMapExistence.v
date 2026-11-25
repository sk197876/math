(** Existence adapter for Federer (1969), 4.1.16,
    p. 373. Reuse the preceding Euclidean closed-set
    nearest-point theorem; no minimisation proof is repeated. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNearestUP WhitneyNearestCenters
  EuclideanConvexNearestMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_convex_nearest_map_exists]: the
    original nearest-point relation has a value for every
    x in Euclidean space, Federer 4.1.16, p. 373.
    The earlier existence theorem even permits nonconvex C;
    convexity is used separately for uniqueness and contraction. *)
Theorem euclidean_convex_nearest_map_exists (R : realType) n
    (C : set (inner_metric_space (@euclidean_inner_productP R n))) :
  closed C -> C !=set0 ->
  exists P, is_euclidean_convex_nearest_map C P.
Proof.
move=> hClosed hNonempty.
have hEach x : exists y,
    is_inner_nearest (@euclidean_inner_productP R n) x C y.
  exact: (@whitney_nearest_point_exists R n C hClosed hNonempty x).
have [P hP] := choice hEach.
exists P; exact: hP.
Qed.
