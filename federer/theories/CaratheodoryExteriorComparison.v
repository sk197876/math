(** Federer (1969), 2.10.6, p. 173:
    Caratheodory projection measure is at most exterior
    diameter measure. Use the preceding covering definitions,
    unchanged convex-hull costs and compact hulls. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  MetricDiameter ConvexHull InnerCompactConvexHull EuclideanConvexDiameter ProjectionMeasureUP ProjectionMeasure
  ProjectionClosedOpenComparison ProjectedVolumeGauge ProjectedExteriorGaugeBound ExteriorMeasureGauge
  ExteriorMeasure ExteriorCompactCoverUP ExteriorCompactCoverAgreement ExteriorDiameterConvexity
  CaratheodoryFamilyReplacement TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_projection_exterior_bound]:
    direct T^m>=C^m edge of the comparison
    diagram in Federer 2.10.6, p. 173.
    Each original compact exterior generator has a
    compact convex hull, eligible in the proved
    closed-convex Caratheodory construction. The hull
    preserves its actual metric diameter and exterior
    cost by 2.10.3, p. 172.
    The projection cost is bounded by that
    cost by 2.10.34, p. 197.
    No measurability, boundedness or finite-mass premise
    is imposed on the final target. *)
Theorem caratheodory_projection_exterior_bound (R : realType) n m (hMN : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @caratheodory_projection_measure R n m A<=@exterior_diameter_measure R n m A.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R n).
apply: (@caratheodory_family_replacement R [the metricType R of X]
  (@nonempty_compact_metric_sets R [the metricType R of X]) (closed_convex_euclidean_sets R n)
  (fun j => val j) (fun j => val j)
  (fun j => exterior_diameter_cost m (val j)) (fun j => projected_volume_gauge m (val j))
  (@exterior_diameter_measure R n m) (@caratheodory_projection_measure R n m)
  (exterior_measure_compact_cover_specification R n m)
  (@caratheodory_projection_closed_cover_specification R n m hMN) _ _ A).
- move=> j; exact: projected_volume_gauge_nonnegative hMN.
- move=> j.
  pose H : set X := @convex_hull R (R_n R n) (val j).
  have hN : H !=set0.
    have [x hx] := (set_valP j).2; exists x; exact: (@convex_hull_includes R (R_n R n) (val j) x hx).
  have hC : compact H.
    exact: (@inner_compact_convex_hull R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n) (val j)
      (@coordinate_basisP R n) (set_valP j).1 (set_valP j).2).
  have hClosed : closed H := compact_closed (@metric_hausdorff R [the metricType R of X]) hC.
  have hConvex : is_inner_convex H := @convex_hull_convex R (R_n R n) (val j).
  pose k : closed_convex_euclidean_sets R n :=
    exist _ H (mem_set (conj hClosed hConvex)).
  exists k; split; first exact: (@convex_hull_includes R (R_n R n) (val j)).
  split.
  + change (is_true (extended_metric_diameter H<=extended_metric_diameter (val j))).
    by rewrite /H euclidean_metric_diameter_convex_hull.
  + have h := @projected_volume_gauge_exterior_bound R n m H hN.
    by rewrite /H exterior_diameter_cost_convex_hull in h.
Qed.
