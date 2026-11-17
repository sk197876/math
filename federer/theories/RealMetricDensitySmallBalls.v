(** Federer 2.10.19(1)-(2), p. 181: the actual real-degree upper density
    gives small-ball bounds, including radius zero. No polynomial or
    integer-degree replacement is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricDensities RealMetricDensityLimits
  RealPower RealPowerRadiusUpperBound RealHausdorffNormalisation
  MetricClosedBalls MeasureUP MeasureBasic PositiveRadiusLimits
  PositiveRadiusLimitBounds ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_metric_density_radius_coefficient]: supporting
    power-cost identity for Federer 2.10.19(1)-(2), p. 181. The ball
    denominator at radius r equals the original diameter normalizer
    times 2^p and r^p. Zero radius and degree zero are included. *)
Lemma real_metric_density_radius_coefficient (R : realType) (p : R)
    (hp : (0<=p)%R) (t r : R) :
    (0<=r)%R ->
    ((real_power 2%R p*t)*(real_hausdorff_normalisation hp*real_power r p))%R=
      (t*(real_hausdorff_normalisation hp*real_power (2*r)%R p))%R.
Proof.
move=> hr; rewrite (@real_power_product R 2%R r p (ler0n R 2) hr).
ring.
Qed.

(** Source for [real_metric_density_small_positive_balls]: supporting
    local bound for Federer 2.10.19(1)-(2), p. 181. The original
    real-degree upper limit supplies one uniform positive scale. *)
Lemma real_metric_density_small_positive_balls (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a (t : R) :
    upper_real_metric_density hp mu a<t%:E ->
    exists e : R, (0<e)%R /\ forall r : R, (0<r<e)%R ->
      mu (metric_closed_ball a r)<=
        (t*(real_hausdorff_normalisation hp*real_power (2*r)%R p))%R%:E.
Proof.
move=> hlim.
have [e [he hsup]] := (positive_radius_upper_lt_iff _ _).1 hlim.
exists e; split=> // r hr.
have hv : positive_radius_values (real_metric_ball_density hp mu a) e
    (real_metric_ball_density hp mu a r) by exists r.
have hq := ltW (le_lt_trans (extended_real_sup_upper hv) hsup).
exact: (@real_metric_ball_density_value_bound R X p hp mu a r t (andP hr).1 hq).
Qed.

(** Source for [real_metric_density_small_nonnegative_balls]: supporting
    radius-zero extension for Federer 2.10.19(1)-(2), p. 181. Monotonicity
    compares the zero-radius ball to every positive one; the proved real
    power continuity bound supplies its limiting cost. The hypothesis
    forces a positive threshold, so no new assumption is added. *)
Lemma real_metric_density_small_nonnegative_balls (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a (t : R) :
    is_measure mu -> upper_real_metric_density hp mu a<t%:E ->
    exists e : R, (0<e)%R /\ forall r : R, (0<=r)%R -> (r<e)%R ->
      mu (metric_closed_ball a r)<=
        (t*(real_hausdorff_normalisation hp*real_power (2*r)%R p))%R%:E.
Proof.
move=> hm hlim.
have [e [he hbound]] := @real_metric_density_small_positive_balls R X p hp mu a t hlim.
have hn := (@real_metric_densities_nonnegative R X p hp mu a hm).2.
have htE := le_lt_trans hn hlim.
have ht : (0<t)%R by move: htE; rewrite lte_fin.
pose C := (real_power 2%R p*t*real_hausdorff_normalisation hp)%R.
have htwo : (0<real_power 2%R p)%R :=
  @real_power_strictly_positive R 2%R p (ltr0n R 2).
have hC : (0<C)%R := mulr_gt0 (mulr_gt0 htwo ht)
  (real_hausdorff_normalisation_positive hp).
have hzero : mu (metric_closed_ball a 0%R)<=
    (t*(real_hausdorff_normalisation hp*real_power (2*0)%R p))%R%:E.
  have hz : mu (metric_closed_ball a 0%R)<=(C*real_power 0%R p)%R%:E.
    apply: (@real_power_positive_radius_upper_at_zero R
      (mu (metric_closed_ball a 0%R)) C e p hC he hp) => r hr.
    have hsub : metric_closed_ball a 0%R `<=` metric_closed_ball a r.
      move=> x hx; exact: le_trans hx (ltW (andP hr).1).
    have hh := le_trans (@measure_mono R X mu hm _ _ hsub) (hbound r hr).
    rewrite -(@real_metric_density_radius_coefficient R p hp t r (ltW (andP hr).1)) in hh.
    by rewrite /C -mulrA.
  rewrite -(@real_metric_density_radius_coefficient R p hp t 0%R (lexx 0%R)).
  by rewrite /C -mulrA in hz.
exists e; split=> // r hr hre.
case: (eqVneq r 0%R)=> [->//|hr0].
have hpos : (0<r)%R by rewrite lt_def hr0 hr.
apply: hbound; by apply/andP.
Qed.
