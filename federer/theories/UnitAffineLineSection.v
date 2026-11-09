(** Federer (1969), 3.3.19, p. 303: actual
    scalar sections of the original bounded open convex
    S along a unit affine line. The topology and
    bounds are proved for the original section itself. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric RealMetricBackground
  InnerConvex CoveringFamilyUP CoveringFamilyLaws MetricBoundedUnion MetricBoundedClosureLaws
  MetricClosedBalls UnitAffineLineGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_affine_line_section_open]: the
    original open S cuts every actual unit affine
    line in an open scalar set, supporting the
    boundary choice in 3.3.19, p. 303. *)
Lemma unit_affine_line_section_open (R:realType) n
    (z u:inner_metric_space (@euclidean_inner_productP R n))
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  inner_norm (@euclidean_inner_productP R n) u= 1 ->open S ->
  @open [the topologicalType of real_line_metric R] [set t|S (z+t*:u)].
Proof.
move=>hu hOpen;apply:(@open_comp [the topologicalType of real_line_metric R]
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] (fun t=>z+t*:u) S).
- by move=>t _;exact:(@unit_affine_line_continuous R n z u hu t).
- exact hOpen.
Qed.

(** Source for [unit_affine_line_section_convex]: actual
    scalar convexity of the original line section,
    supporting the boundary choice in 3.3.19,
    p. 303. This is an exact affine identity. *)
Lemma unit_affine_line_section_convex (R:realType) n
    (z u:R_n R n) (S:set (R_n R n)):
  is_inner_convex S ->@is_inner_convex R R^o [set t:R|S (z+t*:u)].
Proof.
move=>hConvex t s ht hs v hv0 hv1.
have hh:=hConvex (z+t*:u) (z+s*:u) ht hs v hv0 hv1.
rewrite !scalerDr addrACA -scalerDl subrK scale1r !scalerA -scalerDl in hh.
exact hh.
Qed.

(** Source for [unit_affine_line_section_bounded]: original
    boundedness gives boundedness of the actual scalar
    unit-line section in 3.3.19, p. 303.
    No radius bound or endpoint is supplied separately. *)
Lemma unit_affine_line_section_bounded (R:realType) n
    (z u:inner_metric_space (@euclidean_inner_productP R n))
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  inner_norm (@euclidean_inner_productP R n) u= 1 ->metric_set_bounded S ->
  @metric_set_bounded R [the metricType R of real_line_metric R] [set t|S (z+t*:u)].
Proof.
move=>hu hBound.
have [r [hr hRadius]]:=@metric_bounded_distance_bound R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] S z hBound.
have hSubset:[set t:real_line_metric R|S (z+t*:u)] `<=` metric_closed_ball (0:real_line_metric R) r.
  move=>t ht;have hh:=hRadius (z+t*:u) ht.
  have hDistance:=@unit_affine_line_distance R n z u 0 t hu.
  rewrite scale0r addr0 sub0r normrN in hDistance.
  rewrite hDistance in hh.
  change (is_true (`|0-t|<=r));by rewrite sub0r normrN.
exact:(metric_bounded_subset hSubset (@covering_closed_ball_bounded R
  [the metricType R of real_line_metric R] 0 r hr)).
Qed.
