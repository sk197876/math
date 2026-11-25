(** Federer (1969), 2.10.29, p. 193: equal-width interval squares have
    diameter sqrt(2) times the width. The upper bound suffices for the
    finite self-product cover. Work in the actual Euclidean plane with the
    previously proved scalar coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanRealPlane RealMetricBackground CompactIntervalGauge CompactIntervalDiameter MetricDiameterUP
  MetricDiameter MetricDiameterReal HausdorffLengthUP MetricCartesianProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Rectangles.
Variable R : realType.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [euclidean_interval_rectangle]: supporting
    actual coordinate rectangle U times V in
    2.10.29, p. 193, as a subset of R^2. *)
Definition euclidean_interval_rectangle (U V : compact_real_intervals R) : set E :=
  [set p | val U (euclidean_real_plane_first p) /\ val V (euclidean_real_plane_second p)].

(** Source for [euclidean_interval_rectangle_nonempty]: supporting
    nonempty cover generators in 2.10.29, p. 193.
    Degenerate factor intervals remain permitted. *)
Lemma euclidean_interval_rectangle_nonempty (U V : compact_real_intervals R) :
  euclidean_interval_rectangle U V !=set0.
Proof.
have [u hu] := compact_real_interval_nonempty (set_valP U).
have [v hv] := compact_real_interval_nonempty (set_valP V).
exists (euclidean_real_plane_pair u v).
change (val U (euclidean_real_plane_first (euclidean_real_plane_pair u v)) /\
  val V (euclidean_real_plane_second (euclidean_real_plane_pair u v))).
by rewrite
  (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
  (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
Qed.

(** Source for [euclidean_interval_rectangle_generator]: supporting
    inclusion of the actual interval rectangle
    among the nonempty Hausdorff cover generators
    in 2.10.29, p. 193. This merely
    records the proved nonemptiness predicate. *)
Definition euclidean_interval_rectangle_generator (U V : compact_real_intervals R) : @nonempty_metric_sets R [the metricType R of E] :=
  Sub (euclidean_interval_rectangle U V) (mem_set (euclidean_interval_rectangle_nonempty U V)).

(** Source for [euclidean_interval_rectangle_diameter_bound]: direct
    sqrt(2)*r bound for interval squares in
    2.10.29, p. 193. The supporting statement
    allows either interval to have shorter width
    and includes r=0. *)
Lemma euclidean_interval_rectangle_diameter_bound (U V : compact_real_intervals R) (r : R) :
  0<=r ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val U))<=r ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val V))<=r ->
  (@extended_metric_diameter R [the metricType R of E] (euclidean_interval_rectangle U V)<=
    (Num.sqrt 2*r)%:E)%E.
Proof.
move=> hr hU hV.
have hs0 : (0<=Num.sqrt (2 : R)*r)%R := mulr_ge0 (sqrtr_ge0 _) hr.
apply: (metric_diameter_least (extended_metric_diameter_specification (euclidean_interval_rectangle U V))).
- by rewrite lee_fin.
- move=> p q [hpU hpV] [hqU hqV]; rewrite lee_fin.
  have hx := metric_diameter_upper (extended_metric_diameter_specification (val U)) hpU hqU.
  have hy := metric_diameter_upper (extended_metric_diameter_specification (val V)) hpV hqV.
  rewrite (compact_interval_diameter_finite_value (set_valP U)) lee_fin real_line_metric_distanceE in hx.
  rewrite (compact_interval_diameter_finite_value (set_valP V)) lee_fin real_line_metric_distanceE in hy.
  have hxsq : `|euclidean_real_plane_first p-euclidean_real_plane_first q|^+2<=r^+2.
    rewrite (ler_sqr _ _) ?nnegrE ?normr_ge0 //; exact: le_trans hx hU.
  have hysq : `|euclidean_real_plane_second p-euclidean_real_plane_second q|^+2<=r^+2.
    rewrite (ler_sqr _ _) ?nnegrE ?normr_ge0 //; exact: le_trans hy hV.
  rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 // euclidean_real_plane_squared_distance exprMn sqr_sqrtr ?ler0n //.
  have hh := lerD hxsq hysq; lra.
Qed.
End Rectangles.
