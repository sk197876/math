(** Federer (1969), 3.2.46, p. 281: the actual path
    metric induces the usual topology of A. Both identity
    maps are proved continuous, using small original distances
    in the finite technical carrier. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric MetricSubsetBackground RiemannianTensorUP
  RiemannianDistance RiemannianDistanceBasic ExtendedRealUnitCap
  ExtendedRealUnitCapOrder RiemannianMetricCarrier
  RiemannianDistanceTopologyBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Topology.
Context (R : realType) n A g (hg : @is_continuous_riemannian_tensor R n A g).
Local Notation E := (@metric_subset R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] A).
Local Notation M := (riemannian_metric_space hg).

(** Source for [riemannian_chart_to_metric]: the identity
    of the actual chart points, supporting the topology
    assertion of Federer 3.2.46, p. 281. *)
Definition riemannian_chart_to_metric (x : E) : M := x.

(** Source for [riemannian_metric_to_chart]: the reverse
    identity of the actual chart points, supporting the
    topology assertion of Federer 3.2.46, p. 281. *)
Definition riemannian_metric_to_chart (x : M) : E := x.

(** Source for [riemannian_chart_to_metric_continuous]:
    each rho neighbourhood contains an ordinary chart
    neighbourhood, Federer 3.2.46, p. 281. *)
Theorem riemannian_chart_to_metric_continuous :
  continuous riemannian_chart_to_metric.
Proof.
move=> x U hU.
have [e he hBall] := (metricType_numDomainType.nbhs_mdistP
  (riemannian_chart_to_metric x) U).1 hU.
pose q := Order.min e (1/2).
have hq0 : 0 < q by rewrite /q lt_min he /= divr_gt0 // ltr0n.
have hqe : q <= e by rewrite /q ge_min lexx.
have hq1 : q < 1.
  have hHalf : q <= 1/2 by rewrite /q ge_min lexx orbT.
  apply: le_lt_trans hHalf _; by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
have [r [hr hControl]] := @riemannian_euclidean_to_distance_neighbourhood
  R n A g hg (val x) (set_valP x) q hq0.
apply: (metricType_numDomainType.nbhs_mdistP x _).2.
exists r=> // y hy; apply: hBall.
have hy' : inner_norm (@euclidean_inner_productP R n) (val y-val x) < r.
  rewrite -inner_metric_distanceE -metric_subset_distanceE metric_sym; exact hy.
have hOriginal := (hControl (val y) hy').2.
have hCap : mdist (riemannian_chart_to_metric x) (riemannian_chart_to_metric y) < q.
  by rewrite riemannian_metric_small_ball.
exact: lt_le_trans hCap hqe.
Qed.

(** Source for [riemannian_metric_to_chart_continuous]:
    each ordinary neighbourhood contains a rho neighbourhood;
    the positive exit-cost theorem handles distant endpoints,
    Federer 3.2.46, p. 281. *)
Theorem riemannian_metric_to_chart_continuous :
  continuous riemannian_metric_to_chart.
Proof.
move=> x U hU.
have [e he hBall] := (metricType_numDomainType.nbhs_mdistP
  (riemannian_metric_to_chart x) U).1 hU.
have [r [/andP [hr0 hr1] hControl]] := @riemannian_distance_to_euclidean_neighbourhood
  R n A g hg (val x) (set_valP x) e he.
apply: (metricType_numDomainType.nbhs_mdistP x _).2.
exists r=> // y hy; apply: hBall.
have hOriginal : (@riemannian_distance R n A g (val x) (val y) < r%:E)%E.
  by rewrite -(riemannian_metric_small_ball x y hr1).
have hEuclidean := hControl (val y) hOriginal.
change (is_true (inner_norm (@euclidean_inner_productP R n) (val x-val y) < e)).
rewrite -inner_metric_distanceE metric_sym inner_metric_distanceE.
exact hEuclidean.
Qed.
End Topology.
