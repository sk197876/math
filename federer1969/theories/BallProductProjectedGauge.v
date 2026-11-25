(** Federer (1969), 2.10.46, p. 203: the second displayed projected-volume
    estimate for a closed ball S of radius r and a set T of diameter at most
    delta. Write delta=2*r*e; the printed factor (1+delta^2/(4*r^2))^(m/2)
    becomes sqrt(1+e^2)^m. This natural-dimensional form also handles
    dimension zero. Source context and inputs:
    ProductProjectedVolumeBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanSquaredProduct SquaredProductDiameter MetricProductRectangles MetricClosedBalls
  MetricDiameterUP MetricDiameter EuclideanBallDiameter HausdorffDiameterCost
  HausdorffRadiusCost EuclideanClosedBallVolume EuclideanLebesgueDimensions
  ExtendedSupremumPowers ProductProjectedVolumeBound ProjectedVolumeGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ball_product_diameter_bound]: supporting
    squared-diameter estimate in 2.10.46, p. 203,
    with delta=2*r*e. Only an upper bound is needed,
    so the zero-dimensional ball is included. *)
Lemma ball_product_diameter_bound (R : realType) m n
    (a : inner_metric_space (@euclidean_inner_productP R m)) (r e : R)
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  0<=r -> 0<=e -> (extended_metric_diameter T<=((r+r)*e)%:E)%E ->
  (extended_metric_diameter (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) (metric_closed_ball a r) T)<=
    ((r+r)*Num.sqrt (1+e^+2))%:E)%E.
Proof.
move=> hr he hT.
have hrr : 0<=r+r by exact: addr_ge0.
have hsq : 0<=1+e^+2 by exact: addr_ge0 (ler01) (sqr_ge0 e).
apply: (@squared_product_rectangle_diameter_bound R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+n))]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (fun x y=>@euclidean_block_join R m n (x,y)) _ _
  (euclidean_blocks_are_squared_metric_product R m n)
  (metric_closed_ball a r) T (r+r) ((r+r)*e) ((r+r)*Num.sqrt (1+e^+2)))=> //.
- exact: mulr_ge0.
- exact: mulr_ge0 hrr (sqrtr_ge0 _).
- rewrite !exprMn sqr_sqrtr //; nra.
- exact (@metric_ball_diameter_upper R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] a r hr).
Qed.

(** Source for [ball_product_diameter_cost_bound]: supporting
    conversion of the diameter estimate into the factor
    L^m(S)*sqrt(1+e^2)^m in 2.10.46, p. 203. *)
Lemma ball_product_diameter_cost_bound (R : realType) m n
    (a : inner_metric_space (@euclidean_inner_productP R m)) (r e : R)
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  0<=r -> 0<=e -> (extended_metric_diameter T<=((r+r)*e)%:E)%E ->
  (hausdorff_diameter_cost m (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) (metric_closed_ball a r) T)<=
    euclidean_lebesgue_measure m (metric_closed_ball a r)*(Num.sqrt (1+e^+2)^+m)%:E)%E.
Proof.
move=> hr he hT.
have hd := @ball_product_diameter_bound R m n a r e T hr he hT.
have hn := metric_diameter_nonnegative (extended_metric_diameter_specification
  (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) (metric_closed_ball a r) T)).
rewrite /hausdorff_diameter_cost /hausdorff_power_cost.
apply: le_trans (lee_wpmul2l _ (nonnegative_extended_power_monotone m hn hd)) _.
  by rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R m).
rewrite -EFin_expe -EFinM (euclidean_closed_ball_normalized_volume a hr) -EFinM lee_fin.
rewrite exprMn mulrA hausdorff_doubled_radius_normalisation; exact: lexx.
Qed.

(** Source for [ball_product_projected_volume_gauge_bound]: direct
    supremum form of the second displayed estimate in 2.10.46,
    p. 203. The dimension condition ensures the projected-volume
    gauge is nonnegative. This is a generator estimate, not yet
    the limiting product-measure theorem. *)
Theorem ball_product_projected_volume_gauge_bound (R : realType) m n k
    (a : inner_metric_space (@euclidean_inner_productP R m)) (r e : R)
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> 0<=r -> 0<=e -> (extended_metric_diameter T<=((r+r)*e)%:E)%E ->
  (projected_volume_gauge (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) (metric_closed_ball a r) T)<=
    euclidean_lebesgue_measure m (metric_closed_ball a r)*
      (Num.sqrt (1+e^+2)^+m)%:E*projected_volume_gauge k T)%E.
Proof.
move=> hkn hr he hT.
have hS : metric_closed_ball a r !=set0 by exists a; rewrite /metric_closed_ball /= mdistxx.
have hh := @product_projected_volume_gauge_bound R m n k (metric_closed_ball a r) T hS.
apply: le_trans hh _; rewrite [(_*projected_volume_gauge k T)%E]muleC.
apply: lee_wpmul2l; first exact: projected_volume_gauge_nonnegative T hkn.
exact: ball_product_diameter_cost_bound hr he hT.
Qed.
