(** Supporting enlargement for Federer (1969), 2.10.2(2), p. 171: positive
    closed balls can be covered by slightly larger open balls at arbitrarily
    close gauge cost. The geometric ball-diameter factor is an explicit
    proved premise, and may be zero, so dimension zero is included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffMeasureUP HausdorffDiameterCost HausdorffPowerCostLaws
  HausdorffGaugeContinuity RealPowerCoverVariants RealPowerGaugeEnlargement
  MetricRealPowerCost RealPower SphericalOpenBallUP MetricBallDiameterUP MetricClosedBalls
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_ball_real_power_closed_generator_bound]:
    supporting open-ball enlargement step for Federer
    2.10.2(2), p. 171. Compare a closed generator
    strictly below the cutoff and use continuity before
    taking the infimum. Zero diameter and degree zero
    remain subject to the printed conventions. *)
Lemma open_ball_real_power_closed_generator_bound (R : realType) (X : metricType R)
    (c : R) (hc : @is_metric_ball_diameter_factor R X c)
    (coef p : R) (hcoef : (0<coef)%R) (hp : (0<=p)%R) (nu : set X -> \bar R) (A : set X) (t : R) :
  is_metric_scale_envelope (fun j : @positive_open_metric_balls R X => val j)
    (fun j => metric_real_diameter_cost coef p (val j)) t%:E nu ->
  is_positive_metric_closed_ball A -> extended_metric_diameter A<t%:E ->
  nu A<=metric_real_diameter_cost coef p A.
Proof.
move=> hn [a [r [hr hA]]] hcapA.
have hAc : A=metric_closed_ball a r.
  apply/seteqP; split=> x hx; [exact: (hA x).1 hx|exact: (hA x).2 hx].
have hdiam : extended_metric_diameter A=(c*r)%R%:E.
  by rewrite hAc (closed_ball_diameter_factor hc a hr).
rewrite /metric_real_diameter_cost hdiam metric_real_power_cost_finite.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqn]] := @extended_rationals_order_dense R
  (coef*real_power (c*r) p)%:E (nu A) hbad.
have hdt : (c*r<t)%R by move: hcapA; rewrite hdiam lte_fin.
have hb : (coef*real_power (c*r) p<ratr q)%R by move: hq; rewrite lte_fin.
have hc0 : (0<=c)%R := ball_diameter_factor_nonnegative hc.
have [s [hs [hcap hcost]]] := @real_power_gauge_small_enlargement R coef p (c*r)%R t (ratr q)
  hcoef hp (mulr_ge0 hc0 (ltW hr)) hdt hb.
have hc1 : (0<c+1)%R by lra.
pose e : R := (s/(c+1))%R.
have he : (0<e)%R by rewrite /e divr_gt0.
have hce : (c*e<=s)%R.
  have hcl : (c<=c+1)%R by lra.
  have hh := ler_wpM2r (ltW he) hcl.
  have heq : ((c+1)*e=s)%R by rewrite /e mulrC divfK ?gt_eqF.
  by rewrite heq in hh.
have hre : (0<r+e)%R by lra.
pose U := [set x | (mdist a x<r+e)%R].
pose j : @positive_open_metric_balls R X :=
  @exist _ (fun C : set X => C \in [set C | @is_positive_metric_open_ball R X C]) U
    (mem_set (@positive_open_ball_satisfies_laws R X a (r+e)%R hre)).
have hAU : A `<=` U.
  move=> x hx; have hh := (hA x).1 hx; change (is_true (mdist a x<r+e)%R); lra.
have hUdiam : extended_metric_diameter U<=(c*r+s+s)%R%:E.
  rewrite (open_ball_diameter_factor hc a hre) lee_fin mulrDr; lra.
have hsize k : [set j] k -> extended_metric_diameter (val k)<=t%:E.
  move=> ->; apply: le_trans hUdiam _; rewrite lee_fin; exact: ltW hcap.
have hcov : A `<=` \bigcup_(k in [set j]) val k by move=> x hx; exists j=> //; exact: hAU x hx.
have hbound := @metric_scale_envelope_lower R X (@positive_open_metric_balls R X)
  (fun k => val k) (fun k => metric_real_diameter_cost coef p (val k)) t%:E nu hn
  A [set j] (countable1 j) hsize hcov.
rewrite nonnegative_sum_singleton in hbound; last exact: metric_real_diameter_cost_ge0 (ltW hcoef).
have hcostU : metric_real_diameter_cost coef p U<=(coef*real_power (c*r+s+s) p)%:E.
  rewrite /metric_real_diameter_cost -metric_real_power_cost_finite.
  exact (@metric_real_power_cost_monotone R coef p _ _ (ltW hcoef) hp
    (metric_diameter_nonnegative (extended_metric_diameter_specification U)) hUdiam).
have hlt : nu A<(ratr q : R)%:E.
  apply: le_lt_trans (le_trans hbound hcostU) _; by rewrite lte_fin.
by have := lt_trans hqn hlt; rewrite ltxx.
Qed.
