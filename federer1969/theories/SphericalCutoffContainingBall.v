(** Federer (1969), 2.10.42, printed p. 201: replace a small covering set by
    a nearly minimum containing ball before taking covering infima. This
    supporting general-metric lemma bounds a cutoff content using any
    containing ball, enlarged by a positive epsilon so zero radius is
    included without adding radius-zero spherical generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import HausdorffMeasureUP HausdorffDiameterCost HausdorffPowerCostLaws
  HausdorffGaugeContinuity MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP NonnegativeSum NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_cutoff_containing_ball_bound]: supporting
    generator replacement in 2.10.42, p. 201.
    If A is contained in a nonnegative-radius ball
    and twice its radius is strictly below the
    cutoff, the spherical cutoff content of A is at
    most alpha(m) times that radius to power m.
    Only the general bound diameter(B)<=2r is used. *)
Lemma spherical_cutoff_containing_ball_bound (R : realType) (X : metricType R)
    m (nu : set X -> \bar R) (A : set X) (b : X) (r t : R) :
  is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) t%:E nu ->
  A `<=` metric_closed_ball b r -> (0<=r)%R -> (r+r<t)%R ->
  nu A<=hausdorff_power_cost m (r+r)%R%:E.
Proof.
move=> hn hAB hr hrt; rewrite hausdorff_power_cost_finite.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqn]] := @extended_rationals_order_dense R
  (hausdorff_normalisation R m*(r+r)^+m)%:E (nu A) hbad.
have hb : (hausdorff_normalisation R m*(r+r)^+m<ratr q)%R by move: hq; rewrite lte_fin.
have [e [he [hcap hcost]]] := @hausdorff_real_gauge_small_enlargement R m (r+r) t (ratr q) hrt hb.
have hrad : (0<r+e)%R by lra.
pose B := metric_closed_ball b (r+e)%R.
pose j : @positive_closed_metric_balls R X :=
  @exist _ (fun C : set X=>C \in [set C | @is_positive_metric_closed_ball R X C]) B
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
  (fun k=>val k) (fun k=>hausdorff_diameter_cost m (val k)) t%:E nu hn
  A [set j] (countable1 j) hsize hcov.
rewrite nonnegative_sum_singleton in hbound; last exact: hausdorff_diameter_cost_nonnegative.
have hcostB : hausdorff_diameter_cost m B<=(hausdorff_normalisation R m*(r+r+e+e)^+m)%:E.
  rewrite /hausdorff_diameter_cost -hausdorff_power_cost_finite.
  exact (@hausdorff_power_cost_monotone R m _ _
    (metric_diameter_nonnegative (extended_metric_diameter_specification B)) hBdiam).
have hlt : nu A<(ratr q : R)%:E.
  apply: le_lt_trans (le_trans hbound hcostB) _; by rewrite lte_fin.
by have := lt_trans hqn hlt; rewrite ltxx.
Qed.
