(** Small-ball estimates supporting Federer (1969), 2.10.19(1)–(2), p. 181.
    This file proves that extension rather than assuming a bound for a ball
    outside the positive-radius limit range. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MeasureUP MeasureBasic EuclideanBallVolume
  MetricDensities MetricDensityNumericalBounds PositiveRadiusLimits PositiveRadiusLimitBounds PolynomialRadiusUpperBound ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_density_small_positive_balls]: supporting
    small-positive-radius estimate in 2.10.19(1)–(2), p. 181 The strict
    density bound supplies one uniform scale. *)
Lemma metric_density_small_positive_balls (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a (t : R) :
  upper_metric_density m mu a<t%:E -> exists e : R, (0<e)%R /\
    forall r : R, (0<r<e)%R -> mu (metric_closed_ball a r)<=(t*(euclidean_unit_ball_volume R m*r^+m))%:E.
Proof.
move=> hlim.
have [e [he hsup]] := (positive_radius_upper_lt_iff _ _).1 hlim.
exists e; split=> // r hr.
have hv : positive_radius_values (metric_ball_density m mu a) e (metric_ball_density m mu a r).
  by exists r.
have hq := ltW (le_lt_trans (extended_real_sup_upper hv) hsup).
apply: metric_ball_density_value_bound hq; exact: (andP hr).1.
Qed.

(** Source for [metric_density_small_nonnegative_balls]: supporting
    radius-zero extension in 2.10.19(1)–(2), p. 181 Polynomial continuity
    proves the estimate in every degree, retaining the degree-zero value
    0^0=1. *)
Lemma metric_density_small_nonnegative_balls (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a (t : R) :
  is_measure mu -> upper_metric_density m mu a<t%:E -> exists e : R, (0<e)%R /\
    forall r : R, (0<=r)%R -> (r<e)%R ->
      mu (metric_closed_ball a r)<=(t*(euclidean_unit_ball_volume R m*r^+m))%:E.
Proof.
move=> hm hlim.
have [e [he hbound]] := metric_density_small_positive_balls hlim.
have hzero : mu (metric_closed_ball a 0%R)<=(t*(euclidean_unit_ball_volume R m*0^+m))%:E.
  have hz : mu (metric_closed_ball a 0%R)<=((t*euclidean_unit_ball_volume R m)*0^+m)%:E.
    apply: (@polynomial_positive_radius_upper_at_zero R (mu (metric_closed_ball a 0%R))
      (t*euclidean_unit_ball_volume R m)%R e m he)=> r hr.
    have hsub : metric_closed_ball a 0%R `<=` metric_closed_ball a r.
      move=> x hx; exact: le_trans hx (ltW (andP hr).1).
    have hh := le_trans (@measure_mono R X mu hm _ _ hsub) (hbound r hr).
    by rewrite mulrA in hh.
  by rewrite mulrA.
exists e; split=> // r hr hre.
case: (eqVneq r 0%R)=> [->//|hn].
have hp : (0<r)%R by rewrite lt_def hn hr.
apply: hbound; by apply/andP.
Qed.
