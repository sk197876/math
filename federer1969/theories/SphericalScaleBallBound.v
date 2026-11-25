(** Federer (1969), 2.10.27, pp. 190–191: supporting spherical cutoff bound
    for a closed ball section, including a zero-radius tangent section. The
    actual spherical generator family requires strictly positive radii.
    Enlarge the section radius by an arbitrarily small positive amount while
    staying strictly below the cutoff, then use the abstract infimum laws
    and the continuity of the diameter gauge. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls MetricDiameter EuclideanBallDiameter HausdorffMeasureUP
  HausdorffDiameterCost HausdorffRadiusCost HausdorffGaugeContinuity SphericalBallCostBound
  EuclideanBallVolume MetricScaleEnvelopeUP NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_scale_closed_ball_bound]: supporting
    cutoff cost of the sections in 2.10.27,
    pp. 190–191. A strict diameter margin
    permits radius zero without adding zero-radius
    balls to the spherical generator family. The
    ambient metric space is arbitrary. *)
Theorem spherical_scale_closed_ball_bound (R : realType) (X : metricType R)
    k (a : X) (r d : R) (nu : set X -> \bar R) :
  is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>hausdorff_diameter_cost k (val j)) d%:E nu ->
  (0<=r)%R -> (r+r<d)%R ->
  nu (metric_closed_ball a r)<=(euclidean_unit_ball_volume R k*r^+k)%R%:E.
Proof.
move=> hn hr hd; rewrite leNgt; apply/negP=> hbad.
have [q [hbq hqn]] := @extended_rationals_order_dense R
  (euclidean_unit_ball_volume R k*r^+k)%R%:E (nu (metric_closed_ball a r)) hbad.
have hb : (hausdorff_normalisation R k*(r+r)^+k<ratr q)%R.
  rewrite hausdorff_doubled_radius_normalisation; exact hbq.
have [e [he [hcap hcost]]] := @hausdorff_real_gauge_small_enlargement R k (r+r)%R d (ratr q) hd hb.
have hpos : (0<r+e)%R by lra.
pose U := metric_closed_ball a (r+e)%R.
have hU : @is_positive_metric_closed_ball R X U.
  exists a,(r+e)%R; split=> // x; reflexivity.
pose j : @positive_closed_metric_balls R X := Sub U (mem_set hU).
have hdiam : extended_metric_diameter U<=d%:E.
  apply: le_trans (metric_ball_diameter_upper a (ltW hpos)) _.
  rewrite lee_fin; lra.
have hc : metric_closed_ball a r `<=` \bigcup_(i in [set j]) val i.
  move=> x hx; exists j=> //; change (is_true (mdist a x<=r+e)%R).
  apply: le_trans hx _; rewrite lerDl; exact: ltW he.
have hsize (i : @positive_closed_metric_balls R X) (hi : [set j] i) : extended_metric_diameter (val i)<=d%:E.
  by rewrite (hi : i=j).
have hh := @metric_scale_envelope_lower R X (@positive_closed_metric_balls R X)
  (fun i=>val i) (fun i=>hausdorff_diameter_cost k (val i)) d%:E nu hn
  (metric_closed_ball a r) [set j] (countable1 j) hsize hc.
rewrite nonnegative_sum_singleton in hh; last exact: hausdorff_diameter_cost_nonnegative.
have hcostU := @spherical_ball_cost_bound R X k a (r+e)%R hpos.
have hsum : (r+r+e+e=(r+e)+(r+e))%R by lra.
rewrite hsum hausdorff_doubled_radius_normalisation in hcost.
have hcostE : (euclidean_unit_ball_volume R k*(r+e)^+k)%R%:E<(ratr q : R)%:E by rewrite lte_fin.
have hfalse := lt_trans hqn (le_lt_trans (le_trans hh hcostU) hcostE).
by rewrite ltxx in hfalse.
Qed.
