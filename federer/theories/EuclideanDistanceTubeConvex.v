(** Federer (1969), 3.2.35, p. 272:
    the actual distance tubes of an arbitrary
    convex source are convex. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerConvex InnerConvexNeighbourhoods MetricOpenThickening MetricSetDistanceUP MetricDistanceTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_tube_convex]:
    the convexity assertion used in Steiner's
    induction, Federer 3.2.35, p. 272.
    The proved equality with the existing
    metric open thickening permits its actual
    norm-triangle convexity proof to apply.
    The original source need not be closed,
    bounded or measurable. *)
Theorem euclidean_distance_tube_convex (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  is_metric_set_distance S d ->is_inner_convex S ->is_inner_convex [set x|d x<r].
Proof.
move=>hD hS; rewrite (@metric_distance_tube_thickening R _ S d r hD).
exact:(@inner_convex_open_thickening R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) S r hS).
Qed.
