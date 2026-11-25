(** Federer (1969), 2.10.39, printed p. 199: the equally subdivided box is
    covered by closed balls of diameter sqrt(n) times the maximal cell
    width. Derive coverage from the public interval and midpoint-coordinate
    specifications; no partition or centre implementation is inspected.
    Source context and background: RectangularGridUP.v and
    EuclideanCubeRadius.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric EuclideanBoxUP EuclideanCubeRadius
  ScalarIntervalPartitionUP ScalarIntervalPartitionLaws RectangularGridUP
  OrthonormalFamilies MetricClosedBalls Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectangular_grid_ball_cover]: supporting
    finite spherical cover in 2.10.39, p. 199.
    Every side cell has width at most h; a ball
    centred at its specified midpoint contains its
    Cartesian cell. Closed cell endpoints, degenerate
    sides and dimension zero are retained. *)
Theorem rectangular_grid_ball_cover (R : realType) n origin axis c Q
    count node centre (h : R) :
  @is_euclidean_rectangular_box R n origin axis c Q ->
  (forall i, is_equal_interval_partition (c i) (count i) (node i)) ->
  @is_rectangular_grid_centres R n origin axis count node centre ->
  0<=h -> (forall i, c i/(count i)%:R<=h) ->
  Q `<=` \bigcup_s @metric_closed_ball R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    (centre s) (Num.sqrt n%:R*h/2).
Proof.
move=> hQ hP hG hh hw x hx.
have hex i : exists j : 'I_(count i),
    `|euclidean_inner_product (x-origin) (axis i)-(node i j+node i j.+1)/2|<=h/2.
  apply: (@equal_interval_midpoint_cover R (c i) (count i) (node i) (hP i) h _ (hw i)).
  exact: (proj1 (euclidean_box_carrier_law hQ x) hx) i.
pose pick i := projT1 (cid (hex i)).
pose s : rectangular_grid_indices count := [ffun i=>pick i].
have hcoord i : `|euclidean_inner_product (x-centre s) (axis i)|<=h/2.
  have he : x-centre s=(x-origin)-(centre s-origin).
    by rewrite opprB addrA subrK.
  rewrite he (bilBl (@euclidean_inner_bilinear R n)) (hG s i).
  rewrite /s ffunE; exact: (projT2 (cid (hex i))).
have hr : 0<=h/2 by lra.
have hb := @euclidean_frame_cube_norm_bound R n axis (x-centre s) (h/2)
  (euclidean_box_orthonormal_law hQ) hr hcoord.
exists s=> //.
change (is_true (inner_norm (@euclidean_inner_productP R n) (centre s-x)<=Num.sqrt n%:R*h/2)).
rewrite -[centre s-x]opprB inner_normN.
by rewrite mulrA in hb.
Qed.
