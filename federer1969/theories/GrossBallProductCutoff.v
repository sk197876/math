(** Federer (1969), 2.10.46, pp. 203–204: the projection-volume estimate
    applies to Gross coverings. Fix a first-factor ball, cover the second
    factor at scale 2*r*e, and retain the prescribed product cutoff. This is
    the first of the two covering passages in the printed argument, not a
    postulated product-measure identity. Source context:
    BallProductProjectedGauge.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles MetricClosedBalls EuclideanRectangleBorel
  TopologicalBorel BorelCoverCostUP ProjectedVolumeGauge ProjectionMeasure
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanLebesgueDimensions
  BallProductProjectedGauge RectangleScaleSecondFactor MetricDiameter
  MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_ball_product_cutoff_bound]: supporting
    Gross covering estimate from 2.10.46, pp. 203–204,
    for a fixed positive-radius first ball and arbitrary V.
    A positive relative second-factor scale e is retained
    explicitly until the subsequent limiting argument. *)
Theorem gross_ball_product_cutoff_bound (R : realType) m n k
    (a : inner_metric_space (@euclidean_inner_productP R m)) (r e : R)
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta : \bar R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R (m+n))) -> \bar R) :
  (k<=n)%N -> 0<r -> 0<e -> (((r+r)*Num.sqrt (1+e^+2))%:E<=delta)%E ->
  is_metric_scale_envelope
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R (m+n)))=>val j)
    (fun j=>projected_volume_gauge (m+k) (val j)) delta nu ->
  (nu (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) (metric_closed_ball a r) V)<=
    euclidean_lebesgue_measure m (metric_closed_ball a r)*
      (Num.sqrt (1+e^+2)^+m)%:E*@gross_measure R n k V)%E.
Proof.
move=> hkn hr he hdelta hn.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+n))].
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose J := @borel_metric_sets R P.
pose K := @borel_metric_sets R Y.
pose W := fun j : J=>val j.
pose T := fun j : K=>val j.
pose w := fun j : J=>@projected_volume_gauge R (m+n) (m+k) (val j).
pose c := fun j : K=>@projected_volume_gauge R n k (val j).
pose S := metric_closed_ball a r.
have hS : borel_set S := closed_borel_set (@metric_closed_ball_closed R X a r).
pose u (j : K) : J := Sub (metric_product_rectangle
  (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2) S (val j))
  (mem_set (@euclidean_rectangle_borel R m n S (val j) hS (set_valP j))).
pose b := euclidean_unit_ball_volume R m*r^+m*Num.sqrt (1+e^+2)^+m.
have hsq : 0<1+e^+2 by rewrite (lt_le_trans ltr01) // lerDl sqr_ge0.
have hb : 0<b.
  apply: mulr_gt0; last by rewrite exprn_gt0 // sqrtr_gt0.
  apply: mulr_gt0; first exact: (euclidean_unit_ball_volumeE R m).2.
  exact: exprn_gt0.
have heta : (0<((r+r)*e)%:E)%E by rewrite lte_fin mulr_gt0 // addr_gt0.
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
have hw j : (0<=w j)%E := @projected_volume_gauge_nonnegative R (m+n) (m+k) (val j) hdim.
have hd j : (extended_metric_diameter (T j)<=((r+r)*e)%:E)%E ->
    (extended_metric_diameter (W (u j))<=delta)%E.
  move=> hj; apply: le_trans _ hdelta.
  exact (@ball_product_diameter_bound R m n a r e (val j) (ltW hr) (ltW he) hj).
have hc j : (extended_metric_diameter (T j)<=((r+r)*e)%:E)%E -> (w (u j)<=b%:E*c j)%E.
  move=> hj; have hh := @ball_product_projected_volume_gauge_bound R m n k a r e (val j)
    hkn (ltW hr) (ltW he) hj.
  rewrite (euclidean_closed_ball_normalized_volume a (ltW hr)) -EFinM in hh; exact hh.
have hh := @rectangle_scale_second_factor_bound R P X Y
  (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2) S J K W w T c u delta ((r+r)*e)%:E nu
  (@gross_measure R n k) b hn hw (gross_measure_specification R n k) heta hb
  (fun _=>erefl) hd hc V.
rewrite (euclidean_closed_ball_normalized_volume a (ltW hr)) -EFinM; exact hh.
Qed.
