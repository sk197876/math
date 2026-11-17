(** Federer 2.10.42, p. 201: apply the already proved original Jung
    containing ball to the real-degree covering gauge. No geometric
    existence argument is repeated. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealPower
  HausdorffMeasureUP MetricRealPowerCost MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP EuclideanMinimumBallUP BoundedJungBall JungConstant
  RealPowerSphericalContainingBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_cost_finite_scale]: supporting scalar
    connection for Federer 2.10.42, p. 201. A finite nonnegative diameter
    scaled by q has real power cost scaled by q^p. This is the existing
    multiplicative real-power law, including zero diameter and degree zero. *)
Lemma real_power_cost_finite_scale (R : realType) (a p q d : R) :
    (0<=q)%R -> (0<=d)%R ->
    metric_real_power_cost a p (q*d)%R%:E=
      (real_power q p)%:E*metric_real_power_cost a p d%:E.
Proof.
move=> hq hd.
rewrite !metric_real_power_cost_finite -EFinM
  (@real_power_product R q d p hq hd).
congr (_%:E); ring.
Qed.

(** Source for [real_power_jung_spherical_cutoff_bound]: direct
    generator step for the real-degree version of Federer 2.10.42,
    p. 201. Jung supplies the original minimum containing ball. The
    spherical cutoff bound applies to it with the real power gauge.
    Zero radius and zero ambient dimension are retained. *)
Lemma real_power_jung_spherical_cutoff_bound (R : realType) n
    (a p : R) (ha : (0<a)%R) (hp : (0<=p)%R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (d t : R) :
    is_metric_scale_envelope
      (fun j : @positive_closed_metric_balls R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] => val j)
      (fun j => metric_real_diameter_cost a p (val j)) t%:E nu ->
    A !=set0 -> (0<=d)%R -> (@jung_factor R n*d<t)%R ->
    extended_metric_diameter A<=d%:E ->
    nu A<=(real_power (@jung_factor R n) p)%:E*metric_real_power_cost a p d%:E.
Proof.
move=> hn hne hd hcap hdiam.
have [b [r [hmin [hbound _]]]] := @bounded_jung_minimum_ball R n A d hne hd hdiam.
have hr := minimum_ball_radius_nonnegative_law hmin.
have hrt : (r+r<t)%R := le_lt_trans hbound hcap.
have hh := @real_power_spherical_cutoff_containing_ball_bound R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  a p ha hp nu A b r t hn (minimum_ball_contains_law hmin) hr hrt.
have hq := @jung_factor_nonnegative R n.
have hcost : metric_real_power_cost a p (r+r)%R%:E<=
    metric_real_power_cost a p (@jung_factor R n*d)%R%:E.
  apply: (@metric_real_power_cost_monotone R a p _ _ (ltW ha) hp).
  - by rewrite lee_fin addr_ge0.
  - by rewrite lee_fin.
have hb := le_trans hh hcost.
by rewrite (@real_power_cost_finite_scale R a p (@jung_factor R n) d hq hd) in hb.
Qed.
