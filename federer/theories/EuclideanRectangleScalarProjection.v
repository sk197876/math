(** Federer (1969), 3.3.20, p. 307:
    original rectangle projections have their actual weighted endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EuclideanInnerProduct
  InnerMetric EuclideanRealPlane MetricCartesianProductUP EuclideanIntervalRectangles
  ClosedIntervalWeightedSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_rectangle_scalar_projection]: the
    actual scalar projection of an original rectangle
    onto a direction with nonnegative coordinates is
    the interval between its weighted endpoint sums,
    3.3.20, p. 307. Degenerate intervals
    and zero direction coordinates are retained. *)
Theorem euclidean_rectangle_scalar_projection (R:realType)
    (S T:compact_real_intervals R) (a b c d u v:R):
  a<=b ->c<=d ->0<=u ->0<=v ->
  val S=(`[a,b]:set (real_line_metric R)) ->val T=(`[c,d]:set (real_line_metric R)) ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u*euclidean_real_plane_first p+v*euclidean_real_plane_second p) @`
    euclidean_interval_rectangle S T=(`[u*a+v*c,u*b+v*d]:set R).
Proof.
move=>hab hcd hu hv hS hT;apply/seteqP;split=>z.
- move=>[p [hpS hpT] <-].
  rewrite hS /= in_itv /= in hpS.
  rewrite hT /= in_itv /= in hpT.
  rewrite /= in_itv /=;apply/andP;move:hpS hpT=>/andP[h0 h1] /andP[h2 h3];split;nra.
- move=>hz.
  have hBound:u*a+v*c<=z<=u*b+v*d by move:hz;rewrite /= in_itv.
  have [x [y [hx [hy hValue]]]]:=(@closed_interval_weighted_sum R a b c d u v z hab hcd hu hv).1 hBound.
  exists (euclidean_real_plane_pair x y).
  + change (val S (euclidean_real_plane_first (euclidean_real_plane_pair x y)) /\
      val T (euclidean_real_plane_second (euclidean_real_plane_pair x y))).
    rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) hS hT.
    by split.
  + by rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) hValue.
Qed.
