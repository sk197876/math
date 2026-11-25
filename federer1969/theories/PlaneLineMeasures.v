(** Federer (1969), 2.5.10, p. 101: horizontal and vertical tests for the
    representing density. Hausdorff length on each line is L^1 by 2.10.7, p.
    175, and the coordinate isometries. The projected-counting measure
    equals length horizontally and vanishes on vertical segments. Source
    context: HausdorffCoordinateLines.v and PlaneProjectionMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanCoordinateMetric
  EuclideanPlaneCoordinates EuclideanPlaneLines EuclideanCoordinateLineTopology
  HausdorffLength HausdorffCoordinateLines LebesgueScalarMeasure MeasureUP MeasureBasic
  MeasureAlmostBasic TopologicalBorel PlaneProjectionMeasure PlaneProjectionNullImage
  BorelImageCaratheodoryBounds BorelImageCoverCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [plane_horizontal]: the horizontal
    line at height t in the geometric argument of
    Federer 2.5.10, p. 101. *)
Definition plane_horizontal (R : realType) (t s : R) := euclidean_plane_join (s,t).

(** Source for [plane_vertical]: the vertical fibre
    over s in Federer 2.5.10, p. 101. *)
Definition plane_vertical (R : realType) (s t : R) := euclidean_plane_join (s,t).

(** Source for [plane_horizontal_hausdorff]: Hausdorff
    length of any subset of a horizontal line, supporting
    Federer 2.5.10, p. 101, from 2.10.7,
    p. 175. No measurability premise is needed. *)
Lemma plane_horizontal_hausdorff (R : realType) (t : R) (A : set R) :
  hausdorff_length (plane_horizontal t @` A)=lebesgue_scalar_measure A.
Proof.
have he : plane_horizontal t=euclidean_coordinate_line ord0 (euclidean_plane_join (0%R,t)).
  exact: funext (fun s => euclidean_plane_horizontal_line s t).
by rewrite he hausdorff_coordinate_line_measure.
Qed.

(** Source for [plane_vertical_hausdorff]: Hausdorff
    length of any subset of a vertical line, supporting
    Federer 2.5.10, p. 101, from 2.10.7,
    p. 175. *)
Lemma plane_vertical_hausdorff (R : realType) (s : R) (A : set R) :
  hausdorff_length (plane_vertical s @` A)=lebesgue_scalar_measure A.
Proof.
have he : plane_vertical s=euclidean_coordinate_line (lift ord0 ord0) (euclidean_plane_join (s,0%R)).
  exact: funext (fun t => euclidean_plane_vertical_line s t).
by rewrite he hausdorff_coordinate_line_measure.
Qed.

(** Source for [plane_horizontal_segment_borel]:
    measurable finite-line tests for Federer 2.5.10,
    p. 101; the segments are closed and hence Borel. *)
Lemma plane_horizontal_segment_borel (R : realType) (t a b : R) :
  borel_set (plane_horizontal t @` `[a,b]).
Proof.
have he : plane_horizontal t=euclidean_coordinate_line ord0 (euclidean_plane_join (0%R,t)).
  exact: funext (fun s => euclidean_plane_horizontal_line s t).
rewrite he; exact: euclidean_coordinate_segment_borel.
Qed.

(** Source for [plane_vertical_segment_borel]:
    Borel vertical-segment tests for Federer 2.5.10,
    p. 101, by compactness of the parameter interval. *)
Lemma plane_vertical_segment_borel (R : realType) (s a b : R) :
  borel_set (plane_vertical s @` `[a,b]).
Proof.
have he : plane_vertical s=euclidean_coordinate_line (lift ord0 ord0) (euclidean_plane_join (s,0%R)).
  exact: funext (fun t => euclidean_plane_vertical_line s t).
rewrite he; exact: euclidean_coordinate_segment_borel.
Qed.

(** Source for [plane_horizontal_projection_measure]:
    horizontal tests for Federer 2.5.10, p. 101:
    the projected-counting measure equals length on every
    subset of each horizontal line. It is squeezed
    between the projection cost and Hausdorff length. *)
Lemma plane_horizontal_projection_measure (R : realType) (t : R) (A : set R) :
  plane_projection_measure (plane_horizontal t @` A)=lebesgue_scalar_measure A.
Proof.
have he : (@plane_first_projection R) @` (plane_horizontal t @` A)=A.
  apply/seteqP; split.
  - move=> s [x [u hu <-] <-]; by rewrite /plane_first_projection /plane_horizontal euclidean_plane_join_head.
  - move=> s hs; exists (plane_horizontal t s); first by exists s.
    exact: euclidean_plane_join_head.
apply/eqP; rewrite eq_le; apply/andP; split.
- have h := @plane_projection_hausdorff_bound R (plane_horizontal t @` A).
  by rewrite plane_horizontal_hausdorff in h.
- have h := @borel_image_caratheodory_lower_bound R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] R
    (@plane_first_projection R) (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    (plane_horizontal t @` A).
  by rewrite he in h.
Qed.

(** Source for [plane_vertical_segment_projection_null]:
    vertical tests for Federer 2.5.10, p. 101:
    the only nonzero fibre count is over one scalar
    point, which has L^1 measure zero. *)
Lemma plane_vertical_segment_projection_null (R : realType) (s a b : R) :
  plane_projection_measure (plane_vertical s @` `[a,b])=0.
Proof.
apply: plane_projection_null_image; first exact: plane_vertical_segment_borel.
apply: (@measure_null_subset R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  _ [set s] _ (lebesgue_scalar_singleton s)).
move=> y [x [t ht <-] <-]; exact: euclidean_plane_join_head.
Qed.
