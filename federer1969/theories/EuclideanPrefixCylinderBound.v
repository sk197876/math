(** Federer (1969), 3.1.4, p. 215: after estimating the
    prefix and scalar coordinates, bound the remaining coordinates
    by a containing ball and apply the Cartesian measure formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanMetricProduct MetricCartesianProductUP MetricClosedBalls
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanBallBoxBound
  MeasureUP MeasureBasic MeasurePushforward BorelRegularMeasureUP TopologicalBorel
  ProductMeasure ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_prefix_cylinder_bound]: the extension of
    the exceptional-set estimate over the remaining coordinates in
    Federer 3.1.4, p. 215. The set being estimated need not be
    measurable; it is contained in a measurable Cartesian cylinder. *)
Theorem euclidean_prefix_cylinder_bound (R : realType) m n
    (T : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m))) (c r : R) :
  0<=r -> measure_measurable (@euclidean_lebesgue_measure R m) S ->
  (euclidean_lebesgue_measure m S<=(c*r^+m)%R%:E)%E ->
  T `<=` metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R (m+n))) r ->
  (forall h, T h -> S (@euclidean_block_split R m n h).1) ->
  (euclidean_lebesgue_measure (m+n) T<=(c*2^+n*r^+(m+n))%R%:E)%E.
Proof.
move=> hr hS hmass hball hprefix.
pose E k := inner_metric_space (@euclidean_inner_productP R k).
pose B := metric_closed_ball (0 : E n) r.
have hB : measure_measurable (@euclidean_lebesgue_measure R n) B.
  apply: (borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_borel_regular R n)).
  apply: closed_borel_set; exact: metric_closed_ball_closed.
have hzero : @euclidean_block_split R m n 0=(0,0).
  rewrite /euclidean_block_split; congr (_, _); apply/ffunP=> i; by rewrite !ffunE.
have hsub : T `<=` (@euclidean_block_split R m n) @^-1` (S `*` B).
  move=> h ht; split; first exact: hprefix.
  have hh := (metric_product_second_nonexpanding (euclidean_blocks_are_metric_product R m n)).2
    0 h Logic.I Logic.I.
  rewrite hzero /= mul1r in hh; exact: le_trans hh (hball h ht).
have hp := congr1 (fun mu=>mu (S `*` B)) (@euclidean_block_measure R m n).
rewrite /measure_pushforward in hp.
apply: le_trans (measure_mono (euclidean_lebesgue_is_measure R (m+n)) hsub) _.
rewrite hp (product_measure_rectangle_value (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_is_measure R n) hS hB).
have hbm : (euclidean_lebesgue_measure n B<=(2^+n*r^+n)%R%:E)%E.
  rewrite /B euclidean_closed_ball_normalized_volume // lee_fin.
  apply: ler_wpM2r; first by rewrite exprn_ge0.
  exact: euclidean_unit_ball_box_bound.
apply: le_trans (lee_pmul
  (@measure_nonnegative R [the choiceType of E m] _ (euclidean_lebesgue_is_measure R m) S)
  (@measure_nonnegative R [the choiceType of E n] _ (euclidean_lebesgue_is_measure R n) B)
  hmass hbm) _.
rewrite -EFinM lee_fin exprD.
have hid : c*r^+m*(2^+n*r^+n)=c*2^+n*(r^+m*r^+n) by ring.
by rewrite hid.
Qed.
