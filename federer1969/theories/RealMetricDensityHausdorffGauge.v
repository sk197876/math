(** Federer 2.10.19(1)-(2), p. 181: convert the original real-degree
    ball estimate to a small-set diameter-cost bound. The existing
    diameter and measure monotonicity laws provide the geometric step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricDensities RealMetricDensityLimits
  RealMetricDensitySmallBalls RealHausdorffNormalisation RealPower
  MetricRealPowerCost MetricClosedBalls MetricDiameterUP MetricDiameter
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_metric_density_local_set_bound]: supporting
    original small-set estimate in Federer 2.10.19(1)-(2), p. 181.
    A set containing x lies in the closed ball centred at x of radius
    its actual diameter. The separately proved radius-zero connection
    includes nonempty sets of diameter zero and retains degree zero. *)
Lemma real_metric_density_local_set_bound (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) x (t : R) :
    is_measure mu -> upper_real_metric_density hp mu x<t%:E ->
    exists delta : R, (0<delta)%R /\ forall S : set X, S x ->
      extended_metric_diameter S<=delta%:E ->
      mu S<=(real_power 2%R p*t)%R%:E*
        metric_real_diameter_cost (real_hausdorff_normalisation hp) p S.
Proof.
move=> hm hlim.
have [e [he hball]] := @real_metric_density_small_nonnegative_balls R X p hp mu x t hm hlim.
pose delta := (e/2)%R.
have hd0 : (0<delta)%R by rewrite /delta; lra.
have hde : (delta<e)%R by rewrite /delta; lra.
exists delta; split=> // S hx hd.
have hnum : extended_metric_diameter S \is a fin_num.
  rewrite (ge0_fin_numE (metric_diameter_nonnegative (extended_metric_diameter_specification S))).
  exact: le_lt_trans hd (@ltry R delta).
pose d := fine (extended_metric_diameter S).
have hD : extended_metric_diameter S=d%:E by rewrite /d fineK.
have hdnon : (0<=d)%R.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification S).
  by rewrite hD lee_fin in hh.
have hdd : (d<=delta)%R by move: hd; rewrite hD lee_fin.
have hsmall : (d<e)%R := le_lt_trans hdd hde.
have hsub : S `<=` metric_closed_ball x d.
  move=> y hy; have hh := metric_diameter_upper (extended_metric_diameter_specification S) hx hy.
  by rewrite hD lee_fin in hh.
have hb := le_trans (@measure_mono R X mu hm S _ hsub) (hball d hdnon hsmall).
have hcost : metric_real_diameter_cost (real_hausdorff_normalisation hp) p S=
    (real_hausdorff_normalisation hp*real_power d p)%R%:E.
  by rewrite /metric_real_diameter_cost hD metric_real_power_cost_finite.
rewrite hcost -EFinM (@real_metric_density_radius_coefficient R p hp t d hdnon).
exact hb.
Qed.
