(** Federer (1969), 2.10.46, pp. 203–204: the null second-factor case of the
    Caratheodory product assertion. At every target cutoff, a fixed
    sufficiently small positive radius gives null cylinders. Balls with
    centers in a countable dense set cover the first factor. No finiteness
    or measurability of the first factor is needed; dimension zero is
    included. Source context: ConvexBallProductCutoff.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles MetricRectangleFirstSlice MetricClosedBalls
  EuclideanMetricSeparability SeparableClosedCover ProjectionMeasure ProjectionClosedOpenComparison ProjectedVolumeGauge
  ConvexBallProductCutoff CaratheodoryLimitUP MetricScaleCutoffCost
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport
  ExtendedRealOrderTopology ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [caratheodory_projection_product_null_second_factor]: zero
    second-factor consequence of the Caratheodory product statement in
    2.10.46, p. 203, including arbitrary first-factor sets.
    The proof gives zero directly, without using an undefined
    infinity-times-zero expression from 2.1.1. *)
Theorem caratheodory_projection_product_null_second_factor (R : realType) m n k
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> @caratheodory_projection_measure R n k V=0%E -> forall U,
  @caratheodory_projection_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=0%E.
Proof.
move=> hkn hV U.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+n))].
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose first := fun z=>(@euclidean_block_split R m n z).1.
pose second := fun z=>(@euclidean_block_split R m n z).2.
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
apply/eqP; rewrite eq_le (measure_nonnegative (caratheodory_projection_measure_is_measure R hdim)) andbT.
apply: (caratheodory_limit_least (@caratheodory_projection_closed_cover_specification R (m+n) (m+k) hdim))=> delta nu hdelta hn.
have [q [hq hqd]] := @extended_rationals_order_dense R 0%E delta hdelta.
have hq0 : (0<ratr q :>R) by move: hq; rewrite lte_fin.
pose s : R := Num.sqrt (1+1^+2).
have hs : 0<s by rewrite /s expr1n sqrtr_gt0 addr_gt0.
pose r := ratr q/(s+s).
have hss : 0<s+s := addr_gt0 hs hs.
have hr : 0<r := divr_gt0 hq0 hss.
have heq : (r+r)*s=ratr q by rewrite mulrDl -mulrDr /r divfK //; exact: lt0r_neq0 hss.
have hdiam : (((r+r)*s)%:E<=delta)%E by rewrite heq; exact: ltW hqd.
have hnu : is_measure nu.
  apply: (metric_scale_envelope_is_measure hn)=> j.
  exact: projected_volume_gauge_nonnegative hdim.
pose rho := fun A : set X=>nu (metric_product_rectangle first second A V).
have hm := @metric_rectangle_first_slice_is_measure R P X Y first second V nu hnu.
have hball a : rho (metric_closed_ball a r)=0%E.
  have hh := @convex_ball_product_cutoff_bound R m n k a r 1 V delta nu hkn hr ltr01 hdiam hn.
  rewrite hV mule0 in hh; apply/eqP; rewrite eq_le hh (measure_nonnegative hm); reflexivity.
have [D [hD hdense]] := euclidean_metric_separable R m.
have hcov : U `<=` \bigcup_(a in D) metric_closed_ball a r.
  move=> x _; have [a [ha hnear]] := metric_dense_point_near hdense x hr.
  exists a=> //; rewrite /metric_closed_ball /= metric_sym; exact: ltW hnear.
have hh := @measure_indexed_cover R X X rho hm U D (fun a=>metric_closed_ball a r) hD hcov.
by rewrite (nonnegative_sum_zero (fun a _=>hball a)) in hh.
Qed.
