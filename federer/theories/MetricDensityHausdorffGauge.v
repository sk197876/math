(** Gauge conversion for Federer (1969), 2.10.19(1)–(2), p. 181. The
    normalization alpha(m)2^(-m) explains the factor 2^m. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricDensities MetricDensitySmallBalls EuclideanBallVolume HausdorffDiameterCost HausdorffPowerCostLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_density_hausdorff_coefficient]: supporting
    coefficient identity behind the factor 2^m in 2.10.19(1)–(2), p. 181 The
    initial integer degrees include zero. *)
Lemma metric_density_hausdorff_coefficient (R : realType) (m : nat) (t : R) :
  ((2 : R)^+m*t)*hausdorff_normalisation R m=t*euclidean_unit_ball_volume R m.
Proof.
have hn : (2 : R)^+m!=0 by rewrite expf_neq0 // pnatr_eq0.
rewrite /hausdorff_normalisation [(2 : R)^+m*t]mulrC -mulrA.
by rewrite [(2 : R)^+m*(euclidean_unit_ball_volume R m/(2 : R)^+m)]mulrC divfK.
Qed.

(** Source for [metric_density_local_set_bound]: supporting uniform
    small-set estimate used in 2.10.19(1)–(2), p. 181 A set containing x
    lies in B(x,diam S). The separately proved radius-zero extension handles
    nonempty zero-diameter sets with 0^0=1. *)
Lemma metric_density_local_set_bound (R : realType) (X : metricType R)
    m (mu : set X -> \bar R) x (t : R) :
  is_measure mu -> (upper_metric_density m mu x<t%:E)%E ->
  exists delta : R, 0<delta /\ forall S : set X, S x ->
    (extended_metric_diameter S<=delta%:E)%E ->
    (mu S<=((2 : R)^+m*t)%:E*hausdorff_diameter_cost m S)%E.
Proof.
move=> hm hlim.
have [e [he hball]] := metric_density_small_nonnegative_balls hm hlim.
pose delta := e/2.
have hd0 : 0<delta by rewrite /delta; lra.
have hde : delta<e by rewrite /delta; lra.
exists delta; split=> // S hx hd.
have hnum : extended_metric_diameter S \is a fin_num.
  rewrite (ge0_fin_numE (metric_diameter_nonnegative (extended_metric_diameter_specification S))).
  exact: le_lt_trans hd (@ltry R delta).
pose d := fine (extended_metric_diameter S).
have hD : extended_metric_diameter S=d%:E by rewrite /d fineK.
have hdnon : 0<=d.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification S).
  by rewrite hD lee_fin in hh.
have hdd : d<=delta by move: hd; rewrite hD lee_fin.
have hsmall : d<e := le_lt_trans hdd hde.
have hsub : S `<=` metric_closed_ball x d.
  move=> y hy; have hh := metric_diameter_upper (extended_metric_diameter_specification S) hx hy.
  by rewrite hD lee_fin in hh.
have hb := le_trans (@measure_mono R X mu hm S _ hsub) (hball d hdnon hsmall).
have hcost : hausdorff_diameter_cost m S=(hausdorff_normalisation R m*d^+m)%:E.
  by rewrite /hausdorff_diameter_cost hD hausdorff_power_cost_finite.
rewrite hcost -EFinM mulrA metric_density_hausdorff_coefficient -mulrA.
exact hb.
Qed.
