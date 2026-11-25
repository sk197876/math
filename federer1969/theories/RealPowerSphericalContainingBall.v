(** Federer 2.10.42, p. 201: the containing-ball cutoff connection for
    every nonnegative real power. Extend the existing containing-ball
    proof only at its scalar gauge, using the proved real-power small
    enlargement law. Strictly positive spherical radii are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import HausdorffMeasureUP RealPower MetricRealPowerCost
  RealPowerCoverVariants RealPowerGaugeEnlargement MetricClosedBalls
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP NonnegativeSum
  NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_spherical_cutoff_containing_ball_bound]:
    supporting generator replacement in Federer 2.10.42, p. 201, for
    the real-degree gauge of 2.10.2, p. 171. If A is contained in a
    nonnegative-radius ball and twice its radius is strictly below the
    cutoff, the spherical cutoff content is at most the diameter cost
    of twice that radius. Positive enlargements include radius zero
    without adding radius-zero generators. *)
Lemma real_power_spherical_cutoff_containing_ball_bound (R : realType)
    (X : metricType R) (a p : R) (ha : (0<a)%R) (hp : (0<=p)%R)
    (nu : set X -> \bar R) (A : set X) (b : X) (r t : R) :
    is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
      (fun j => metric_real_diameter_cost a p (val j)) t%:E nu ->
    A `<=` metric_closed_ball b r -> (0<=r)%R -> (r+r<t)%R ->
    nu A<=metric_real_power_cost a p (r+r)%R%:E.
Proof.
move=> hn hAB hr hrt; rewrite metric_real_power_cost_finite.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqn]] := @extended_rationals_order_dense R
  (a*real_power (r+r) p)%R%:E (nu A) hbad.
have hb : (a*real_power (r+r) p<ratr q)%R by move: hq; rewrite lte_fin.
have [e [he [hcap hcost]]] := @real_power_gauge_small_enlargement R
  a p (r+r) t (ratr q) ha hp (addr_ge0 hr hr) hrt hb.
have hrad : (0<r+e)%R by lra.
pose B := metric_closed_ball b (r+e)%R.
pose j : @positive_closed_metric_balls R X :=
  @exist _ (fun C : set X => C \in [set C | @is_positive_metric_closed_ball R X C]) B
    (mem_set (positive_closed_ball_satisfies_laws b hrad)).
have hcover : A `<=` B.
  move=> x hx; have hh := hAB x hx.
  change (is_true (mdist b x<=r)%R) in hh.
  change (is_true (mdist b x<=r+e)%R); lra.
have hBdiam : extended_metric_diameter B<=(r+r+e+e)%R%:E.
  apply: (metric_diameter_least (extended_metric_diameter_specification B)).
  - rewrite lee_fin; lra.
  - move=> x y hx hy; rewrite lee_fin.
    have hh := metric_closed_ball_diameter_bound hx hy; lra.
have hsize k : [set j] k -> extended_metric_diameter (val k)<=t%:E.
  move=> ->; apply: le_trans hBdiam _; rewrite lee_fin; exact: ltW hcap.
have hcov : A `<=` \bigcup_(k in [set j]) val k.
  move=> x hx; exists j=> //; exact: hcover x hx.
have hbound := @metric_scale_envelope_lower R X (@positive_closed_metric_balls R X)
  (fun k => val k) (fun k => metric_real_diameter_cost a p (val k)) t%:E nu hn
  A [set j] (countable1 j) hsize hcov.
rewrite nonnegative_sum_singleton in hbound;
  last exact: metric_real_diameter_cost_ge0 (ltW ha).
have hcostB : metric_real_diameter_cost a p B<=
    (a*real_power (r+r+e+e) p)%R%:E.
  rewrite /metric_real_diameter_cost -metric_real_power_cost_finite.
  exact: (@metric_real_power_cost_monotone R a p _ _ (ltW ha) hp
    (metric_diameter_nonnegative (extended_metric_diameter_specification B)) hBdiam).
have hlt : nu A<(ratr q : R)%:E.
  apply: le_lt_trans (le_trans hbound hcostB) _; by rewrite lte_fin.
by have := lt_trans hqn hlt; rewrite ltxx.
Qed.
