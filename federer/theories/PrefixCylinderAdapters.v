(** Federer (1969), 3.1.4, p. 215: the containing cylinder
    estimate with a variable prefix length in a fixed ambient dimension.
    These are proved adapters to the usual block measure formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanPrefixTranslation EuclideanBlockCoordinates
  EuclideanPrefixCylinderBound EuclideanMetricProduct MetricCartesianProductUP
  MetricClosedBalls MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_prefix_restriction_ball]: the retained
    coordinates of an increment in B(0,r) remain in their own
    radius-r ball, supporting Federer 3.1.4, p. 215. *)
Lemma euclidean_prefix_restriction_ball (R : realType) m k
    (hk : (k<=m)%N) (h : R_n R m) r :
  metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R m)) r h ->
  metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R k)) r
    (euclidean_prefix_restriction hk h).
Proof.
have hn : m=(k+(m-k))%N by rewrite addnC subnK.
move: hk h; rewrite hn=> hk h hh.
rewrite euclidean_prefix_restriction_blocks.
have hz : @euclidean_block_split R k (m-k) 0=(0,0).
  rewrite /euclidean_block_split; congr (_, _); apply/ffunP=> j; by rewrite !ffunE.
have hb := (metric_product_first_nonexpanding
  (euclidean_blocks_are_metric_product R k (m-k))).2 0 h Logic.I Logic.I.
rewrite hz /= mul1r in hb; exact: le_trans hb hh.
Qed.

(** Source for [euclidean_prefix_restriction_cylinder_bound]:
    extend the prefix estimate over the remaining m-k coordinates,
    Federer 3.1.4, p. 215. The exceptional set need not be measurable. *)
Theorem euclidean_prefix_restriction_cylinder_bound (R : realType) m k
    (hk : (k<=m)%N)
    (T : set (inner_metric_space (@euclidean_inner_productP R m)))
    (S : set (inner_metric_space (@euclidean_inner_productP R k))) (c r : R) :
  0<=r -> measure_measurable (@euclidean_lebesgue_measure R k) S ->
  (euclidean_lebesgue_measure k S<=(c*r^+k)%R%:E)%E ->
  T `<=` metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R m)) r ->
  (forall h, T h -> S (euclidean_prefix_restriction hk h)) ->
  (euclidean_lebesgue_measure m T<=(c*2^+(m-k)*r^+m)%R%:E)%E.
Proof.
have hn : m=(k+(m-k))%N by rewrite addnC subnK.
move: hk T; rewrite hn=> hk T hr hS hmass hball hprefix.
rewrite addKn.
apply: (@euclidean_prefix_cylinder_bound R k (m-k) T S c r hr hS hmass hball).
move=> h hh; have hp := hprefix h hh.
by rewrite euclidean_prefix_restriction_blocks in hp.
Qed.
