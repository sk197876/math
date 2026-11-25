(** Supporting normalized-ball inequalities for Federer (1969), 2.10.19, p.
    181. This file treats the initial integer degrees; zero radius is
    handled separately by polynomial continuity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDensities MetricClosedBalls MeasureUP MeasureBasic EuclideanBallVolume
  PositiveRadiusLimits PositiveRadiusLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_ball_density_nonnegative]: supporting
    nonnegative normalized ball values in 2.10.19,
    p. 181. Only positive radii are required. *)
Lemma metric_ball_density_nonnegative (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a r :
  is_measure mu -> (0<r)%R -> 0<=metric_ball_density m mu a r.
Proof.
move=> hm hr; rewrite /metric_ball_density; apply: mule_ge0.
- exact: (@measure_nonnegative R X mu hm (metric_closed_ball a r)).
- rewrite inve_ge0 lee_fin; exact: ltW (metric_ball_density_denominator_positive m hr).
Qed.

(** Source for [metric_densities_nonnegative]: supporting
    nonnegative upper and lower densities in 2.10.19,
    p. 181. Positive radii provide an actual domain
    at every scale, including at isolated points. *)
Lemma metric_densities_nonnegative (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a : is_measure mu ->
  0<=lower_metric_density m mu a /\ 0<=upper_metric_density m mu a.
Proof.
move=> hm; have hl : 0<=lower_metric_density m mu a.
  apply: positive_radius_lower_nonnegative=> r hr; exact: metric_ball_density_nonnegative hm hr.
split=> //; exact: le_trans hl (metric_densities_ordered m mu a).
Qed.

(** Source for [metric_ball_density_value_bound]: supporting conversion from
    a density bound to a small-ball mass bound in 2.10.19(1)–(2), p. 181
    Finite positive normalisation permits an infinite numerator. *)
Lemma metric_ball_density_value_bound (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a (r t : R) :
  (0<r)%R -> metric_ball_density m mu a r<=t%:E ->
  mu (metric_closed_ball a r)<=(t*(euclidean_unit_ball_volume R m*r^+m))%:E.
Proof.
move=> hr hq.
pose d := (euclidean_unit_ball_volume R m*r^+m)%R.
have hp : (0<d)%R := metric_ball_density_denominator_positive m hr.
have hd : 0<=d%:E by rewrite lee_fin; exact: ltW hp.
have hh := lee_wpmul2r hd hq.
rewrite /metric_ball_density inver (gt_eqF hp) -muleA -!EFinM mulVf ?gt_eqF // mule1 in hh.
exact hh.
Qed.

(** Source for [metric_ball_density_value_large]: supporting large-ball
    estimate in 2.10.19(3), p. 181 The denominator is strictly positive
    finite, irrespective of ball diameter. *)
Lemma metric_ball_density_value_large (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) a (r t : R) :
  (0<r)%R -> t%:E<metric_ball_density m mu a r ->
  (t*(euclidean_unit_ball_volume R m*r^+m))%:E<mu (metric_closed_ball a r).
Proof.
move=> hr hq.
pose d := (euclidean_unit_ball_volume R m*r^+m)%R.
have hp : (0<d)%R := metric_ball_density_denominator_positive m hr.
have hd : 0<d%:E by rewrite lte_fin.
have hh : t%:E*d%:E<metric_ball_density m mu a r*d%:E.
  by rewrite lte_pmul2r ?fin_numE.
rewrite /metric_ball_density inver (gt_eqF hp) -muleA -!EFinM mulVf ?gt_eqF // mule1 in hh.
exact hh.
Qed.
