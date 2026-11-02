(** Federer (1969), 3.2.35, p. 272:
    actual line sections over interior projection
    points are nonempty bounded open convex intervals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  InnerConvex EuclideanProjectionSpace EuclideanProjectionMetric ProjectionLineNormalUP ProjectionLineFibre
  NormMetricScaleContinuity MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws MetricBoundedUnion
  MetricBoundedClosureLaws RealOpenIntervals ScalarOpenConvexInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_line_continuous]: supporting
    the scalar fibre topology in Federer 3.2.35,
    p. 272. The actual unit-line distance
    identity gives continuity with its precise
    scalar and Euclidean topologies. *)
Lemma projection_line_continuous (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w (a:R_n R k.+1):
  is_projection_line_normal p w ->
  continuous (fun t:real_line_metric R=>(a+t*:w:inner_metric_space (@euclidean_inner_productP R k.+1))).
Proof.
move=>hW.
apply:(@metric_fixed_lipschitz_continuous R [the metricType R of real_line_metric R]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R k.+1)]
  (fun t=>a+t*:w) 1 ler01)=>t s.
by rewrite (@projection_line_distance R k p w a t s hW) real_line_metric_distanceE mul1r.
Qed.

(** Source for [projection_line_section_open]: original
    openness gives an open scalar line section,
    supporting the two endpoints in Federer 3.2.35,
    p. 272. The source set is unchanged. *)
Lemma projection_line_section_open (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  is_projection_line_normal p w ->open S ->
  @open [the topologicalType of real_line_metric R] [set t|S (a+t*:w)].
Proof.
move=>hW hOpen.
apply:(@open_comp [the topologicalType of real_line_metric R]
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R k.+1)]
  (fun t=>a+t*:w) S).
- by move=>t _; exact:(@projection_line_continuous R k p w a hW t).
- exact hOpen.
Qed.

(** Source for [projection_line_section_convex]: the
    original convex body cuts each actual affine
    fibre in a convex scalar set, Federer
    3.2.35, p. 272. Exact vector algebra
    transfers every original convex combination. *)
Lemma projection_line_section_convex (R:realType) k
    (w a:R_n R k.+1) (S:set (R_n R k.+1)):
  is_inner_convex S ->@is_inner_convex R R^o [set t:R|S (a+t*:w)].
Proof.
move=>hConvex t s ht hs v hv0 hv1.
have hh:=hConvex (a+t*:w) (a+s*:w) ht hs v hv0 hv1.
rewrite !scalerDr addrACA -scalerDl subrK scale1r !scalerA -scalerDl in hh.
exact hh.
Qed.

(** Source for [projection_line_section_bounded]: actual
    source boundedness bounds the scalar section
    in Federer 3.2.35, p. 272. The
    unit-line isometry identifies |t| with the
    distance from the chosen fibre base point.
    No scalar endpoint bound is added as a premise. *)
Lemma projection_line_section_bounded (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  is_projection_line_normal p w ->metric_set_bounded S ->
  @metric_set_bounded R [the metricType R of real_line_metric R] [set t|S (a+t*:w)].
Proof.
move=>hW hBound.
have [r [hr hRadius]]:=@metric_bounded_distance_bound R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R k.+1)] S a hBound.
have hSubset:[set t:real_line_metric R|S (a+t*:w)] `<=` metric_closed_ball (0:real_line_metric R) r.
  move=>t ht; have hh:=hRadius (a+t*:w) ht.
  have hDistance:=@projection_line_distance R k p w a 0 t hW.
  rewrite scale0r addr0 sub0r normrN in hDistance.
  rewrite hDistance in hh.
  change (is_true (`|0-t|<=r)); by rewrite sub0r normrN.
exact:(metric_bounded_subset hSubset (@covering_closed_ball_bounded R
  [the metricType R of real_line_metric R] 0 r hr)).
Qed.

(** Source for [projection_open_convex_line_interval]: the
    actual bounded open interval on a fibre
    meeting S in Federer 3.2.35, p. 272.
    Its infimum is negative and supremum positive
    relative to an original base point a in S.
    All scalar interval and endpoint laws are
    proved from the original hypotheses. *)
Theorem projection_open_convex_line_interval (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  is_projection_line_normal p w ->S a ->open S ->is_inner_convex S ->metric_set_bounded S ->
  let A:set (real_line_metric R):=[set t|S (a+t*:w)] in
  inf A<0 /\0<sup A /\A=real_open_interval (inf A) (sup A).
Proof.
move=>hW ha hOpen hConvex hBound A.
have hZero:A 0 by change (S (a+0*:w)); rewrite scale0r addr0.
have hNonempty:A!=set0 by exists 0.
have hOpenA:=@projection_line_section_open R k p w a S hW hOpen.
have hConvexA:=@projection_line_section_convex R k w a S hConvex.
have hBoundA:=@projection_line_section_bounded R k p w a S hW hBound.
have [hLower hUpper]:=@scalar_open_member_strict_bounds R A 0 hOpenA hBoundA hZero.
have [_ hInterval]:=@scalar_open_convex_interval R A hNonempty hOpenA hConvexA hBoundA.
by split=>//; split.
Qed.
