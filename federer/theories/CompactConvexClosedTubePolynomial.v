(** Closed Euclidean tubes supporting the coefficient argument
    in Federer (1969), 3.2.45, pp. 279–280.
    Reuse the proved original Steiner formula of
    3.2.35, pp. 271–272. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CompactSetDistanceProfile MetricSetDistanceUP MetricSetDistanceBasic EuclideanClosedDistanceNearest
  EuclideanDistanceTubeBoundary EuclideanDistanceTubeConvex EuclideanConvexClosureVolume
  ConvexSteinerTubeFormula SteinerTubePolynomial CompactMetricBounded VectorSetSum EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_ball_vector_sum_tube]: supporting
    closed-tube identity for Federer 3.2.45, pp. 279–280,
    from the nearest-point result in 3.2.34, p. 271.
    The original closed source plus the closed radius-r
    ball is exactly its distance sublevel. The witness
    is a local nearest point; no regularity of a
    boundary or positive ambient dimension is required. *)
Lemma euclidean_closed_ball_vector_sum_tube (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (d : R_n R n -> R) (r : R) :
  closed S -> S !=set0 -> is_metric_set_distance S d ->
  [set x | d x<=r]=vector_set_sum S [set y | inner_norm (@euclidean_inner_productP R n) y<=r].
Proof.
move=> hClosed hNonempty hDistance; apply/seteqP; split=> x.
- move=> hx; have [a [ha hNearest]] := euclidean_closed_distance_nearest x hClosed hNonempty hDistance.
  apply/vector_set_sum_membership; exists a,(x-a); split=> //; split.
  + change (is_true (inner_norm (@euclidean_inner_productP R n) (x-a)<=r)); by rewrite -hNearest.
  + by rewrite addrC subrK.
- move=> /vector_set_sum_membership [a [b [ha [hb ->]]]].
  have h := metric_set_distance_lower hDistance (a+b) ha.
  have hDifference : (a+b)-a=b by rewrite addrAC subrr add0r.
  rewrite inner_metric_distanceE hDifference in h.
  exact: le_trans h hb.
Qed.

(** Source for [compact_convex_closed_tube_polynomial]: supporting
    actual closed-tube volume in the section comparison of
    Federer 3.2.45, pp. 279–280. The whole positive
    distance sublevel is the closure of the open tube.
    The proved convex closure-volume equality and the
    complete original Steiner polynomial give its exact
    volume. Thin bodies and ambient dimension zero remain. *)
Theorem compact_convex_closed_tube_polynomial (R : realType) n
    (S : compact_metric_set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  is_inner_convex (val S) -> 0<r ->
  @euclidean_lebesgue_measure R n [set x | compact_set_distance_profile S x<=r]=
    steiner_tube_polynomial (val S) r.
Proof.
move=> hConvex hr.
pose d := compact_set_distance_profile S.
have hDistance := compact_set_distance_profile_specification S.
have hNonempty : [set x | d x<r] !=set0.
  have [a ha] := (set_valP S).2; exists a.
  change (is_true (d a<r)); by rewrite /d ((compact_set_distance_profile_zero S a).2 ha).
have hTubeConvex := @euclidean_distance_tube_convex R n (val S) d r hDistance hConvex.
rewrite -(@euclidean_distance_tube_closure R n (val S) d r (set_valP S).2 hDistance hr).
rewrite (euclidean_convex_closure_volume hNonempty hTubeConvex).
exact: (@convex_steiner_tube_formula R n (val S) d (set_valP S).2 hConvex
  (compact_metric_diameter_finite S) hDistance r hr).
Qed.
