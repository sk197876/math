(** Federer 2.10.27, p. 191: convert actual diameter costs of balls
    to alpha(p) r^p in every nonnegative real degree. Use the diameter
    upper bound in arbitrary metric spaces; retain actual diameter. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology ring.
From Federer Require Import RealHausdorffNormalisation RealHausdorffBallCoefficient
  RealPower MetricRealPowerCost MetricDiameterUP MetricDiameter MetricClosedBalls
  EuclideanBallDiameter SphericalBallCostBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_doubled_radius_normalisation]: the
    equality alpha(p) r^p for the cost of a diameter 2r in Federer
    2.10.27, p. 191. Include zero p and zero r with 0^0=1. *)
Lemma real_hausdorff_doubled_radius_normalisation (R : realType) (p : R)
    (hp : (0 <= p)%R) (r : R) : (0 <= r)%R ->
    (real_hausdorff_normalisation hp*real_power (r+r) p =
      real_hausdorff_ball_coefficient hp*real_power r p)%R.
Proof.
move=> hr; have he : (r+r = 2*r)%R by ring.
by rewrite he real_power_product ?ler0n // mulrA real_hausdorff_ball_coefficient_cost.
Qed.

(** Source for [real_spherical_ball_cost_bound]: supporting ball-cost
    bound in Federer 2.10.27, p. 191. An arbitrary metric closed ball
    may have diameter less than 2r. The inequality uses its actual
    diameter and the original real-degree normalization. *)
Lemma real_spherical_ball_cost_bound (R : realType) (X : metricType R)
    (p : R) (hp : (0 <= p)%R) (a : X) (r : R) : (0 < r)%R ->
    metric_real_diameter_cost (real_hausdorff_normalisation hp) p
      (metric_closed_ball a r) <=
    (real_hausdorff_ball_coefficient hp*real_power r p)%R%:E.
Proof.
move=> hr.
have hd := @metric_ball_diameter_upper R X a r (ltW hr).
have hh := @metric_real_power_cost_monotone R (real_hausdorff_normalisation hp) p
  _ _ (ltW (real_hausdorff_normalisation_positive hp)) hp
  (metric_diameter_nonnegative (extended_metric_diameter_specification (metric_closed_ball a r))) hd.
rewrite metric_real_power_cost_finite
  (@real_hausdorff_doubled_radius_normalisation R p hp r (ltW hr)) in hh.
exact: hh.
Qed.
