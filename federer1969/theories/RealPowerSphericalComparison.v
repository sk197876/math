(** Federer (1969), 2.10.2(2), p. 171, last display: H^m <= S^m <= 2^m H^m.
    Here the radius is enlarged positively before taking the infimum, so the
    proof retains Federer's strictly positive radii (2.8.1, p. 141), even
    for singleton generators of diameter zero. No radius-zero ball or
    identity between radius and diameter is assumed. All nonnegative real degrees are
    treated, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost HausdorffPowerCostLaws HausdorffGaugeContinuity
  RealPowerCoverVariants RealPowerGaugeEnlargement RealPower MetricRealPowerCost
  MetricRealPowerMeasureUP MetricRealPowerMeasure HausdorffSphericalComparison
  MetricClosedBalls MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleMeasureBound
  CaratheodoryLimitUP CaratheodoryBorelRegular CaratheodoryTransport
  MeasureUP FiniteMeasureScaling NonnegativeSum NonnegativeSumSupport ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_le_spherical]: direct first
    inequality of Federer 2.10.2(2), p. 171 Restricting the admissible
    covering family increases the infimum. *)
Theorem metric_real_power_le_spherical (R : realType) (X : metricType R)
    (a p : R) (ha : (0<a)%R) (hp : (0<=p)%R) (A : set X) :
  @metric_real_power_measure R X a p A<=@spherical_metric_real_power_measure R X a p A.
Proof.
have hh := @caratheodory_limit_transport R X X
  (@positive_closed_metric_balls R X) (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => val j)
  (fun j => metric_real_diameter_cost a p (val j))
  (fun j => metric_real_diameter_cost a p (val j)) id (@spherical_generator_forget R X)
  (@spherical_metric_real_power_measure R X a p) (@metric_real_power_measure R X a p)
  (@spherical_metric_real_power_specification R X a p) (@metric_real_power_measure_specification R X a p).
have hb : @metric_real_power_measure R X a p (id @` A)<=@spherical_metric_real_power_measure R X a p A.
  apply: hh.
  - move=> j; exact: metric_real_diameter_cost_ge0 (ltW ha).
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
by rewrite image_id in hb.
Qed.

(** Source for [metric_real_power_cost_double]: supporting factor 2^m in
    Federer 2.10.2(2), p. 171 Finite real diameters suffice after choosing a
    finite cutoff. *)
Lemma metric_real_power_cost_double (R:realType) (a p d:R):
  (0<=d)%R -> metric_real_power_cost a p (d+d)%R%:E=
    (real_power 2 p)%:E*metric_real_power_cost a p d%:E.
Proof.
move=>hd; rewrite !metric_real_power_cost_finite -EFinM.
have he:(d+d = 2*d)%R by lra.
rewrite he real_power_product ?ler0n //.
by rewrite mulrCA mulrA.
Qed.

(** Source for [spherical_metric_real_power_scale_bound]: supporting centered-ball
    comparison in Federer 2.10.2(2), p. 171 Infima of strictly positive
    enlarged radii handle zero-diameter generators uniformly, without
    inserting radius-zero balls. *)
Lemma spherical_metric_real_power_scale_bound (R : realType) (X : metricType R)
    (a p : R) (ha : (0<a)%R) (hp : (0<=p)%R) (nu : set X -> \bar R) (A : set X) (d t : R) :
  is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
    (fun j => metric_real_diameter_cost a p (val j)) t%:E nu ->
  A !=set0 -> (0<=d)%R -> (d+d<t)%R -> extended_metric_diameter A<=d%:E ->
  nu A<=metric_real_power_cost a p (d+d)%R%:E.
Proof.
move=> hn [x0 hx0] hd hdt hdiam; rewrite metric_real_power_cost_finite.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqn]] := @extended_rationals_order_dense R
  (a*real_power (d+d) p)%:E (nu A) hbad.
have hb : (a*real_power (d+d) p<ratr q)%R by move: hq; rewrite lte_fin.
have [r [hr [hcap hcost]]] := @real_power_gauge_small_enlargement R a p (d+d) t (ratr q) ha hp (addr_ge0 hd hd) hdt hb.
have hdr : (0<d+r)%R by lra.
pose B := metric_closed_ball x0 (d+r)%R.
pose j : @positive_closed_metric_balls R X :=
  @exist _ (fun C : set X => C \in [set C | @is_positive_metric_closed_ball R X C]) B
    (mem_set (positive_closed_ball_satisfies_laws x0 hdr)).
have hAB : A `<=` B.
  move=> x hx; change (is_true (mdist x0 x<=d+r)%R).
  have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification A) hx0 hx) hdiam.
  have hax : (mdist x0 x<=d)%R by move: hh; rewrite lee_fin.
  lra.
have hBdiam : extended_metric_diameter B<=(d+d+r+r)%R%:E.
  apply: (metric_diameter_least (extended_metric_diameter_specification B)).
  - rewrite lee_fin; lra.
  - move=> x y hx hy; rewrite lee_fin.
    have hh := metric_closed_ball_diameter_bound hx hy; lra.
have hsize k : [set j] k -> extended_metric_diameter (val k)<=t%:E.
  move=> ->; apply: le_trans hBdiam _; rewrite lee_fin; exact: ltW hcap.
have hcov : A `<=` \bigcup_(k in [set j]) val k.
  move=> x hx; exists j=> //; exact: hAB x hx.
have hbound := @metric_scale_envelope_lower R X (@positive_closed_metric_balls R X)
  (fun k => val k) (fun k => metric_real_diameter_cost a p (val k)) t%:E nu hn
  A [set j] (countable1 j) hsize hcov.
rewrite nonnegative_sum_singleton in hbound; last exact: metric_real_diameter_cost_ge0 (ltW ha).
have hcostB : metric_real_diameter_cost a p B<=(a*real_power (d+d+r+r) p)%:E.
  rewrite /metric_real_diameter_cost -metric_real_power_cost_finite.
  exact (@metric_real_power_cost_monotone R a p _ _ (ltW ha) hp
    (metric_diameter_nonnegative (extended_metric_diameter_specification B)) hBdiam).
have hlt : nu A<(ratr q : R)%:E.
  apply: le_lt_trans (le_trans hbound hcostB) _; by rewrite lte_fin.
by have := lt_trans hqn hlt; rewrite ltxx.
Qed.

(** Source for [spherical_metric_real_power_le_double]: direct
    second inequality of Federer 2.10.2(2), p. 171 Strictly positive
    enlarged balls are used before taking the infimum, including at degree
    zero and diameter zero. *)
Theorem spherical_metric_real_power_le_double (R : realType) (X : metricType R)
    (a p : R) (ha : (0<a)%R) (hp : (0<=p)%R) (A : set X) :
  @spherical_metric_real_power_measure R X a p A<=(real_power 2 p)%:E*@metric_real_power_measure R X a p A.
Proof.
have hm := @metric_real_power_measure_specification R X a p.
have hn := @spherical_metric_real_power_specification R X a p.
pose factor : R := (real_power 2 p)%R.
have hc : (0<factor)%R by apply:real_power_strictly_positive; rewrite ltr0n.
have hci : (0<=factor^-1)%R by rewrite invr_ge0; exact: ltW hc.
have hcE : 0<=factor%:E by rewrite lee_fin; exact: ltW hc.
have hciE : 0<=((factor^-1)%R)%:E by rewrite lee_fin.
apply: (caratheodory_limit_least hn)=> tau xi htau hxi.
have [n hnt] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((n.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose psi := metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
  (fun j => metric_real_diameter_cost a p (val j)) t%:E.
have hpsi := @metric_scale_envelope_specification R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) t%:E.
have hpsi_measure : is_measure psi := @metric_scale_envelope_measure R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) t%:E
  (fun j => metric_real_diameter_cost_ge0 p (val j) (ltW ha)).
pose phi := metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
  (fun j => metric_real_diameter_cost a p (val j)) ((t/4)%R%:E).
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) ((t/4)%R%:E).
have hgen (j : @nonempty_metric_sets R X) : extended_metric_diameter (val j)<=(t/4)%R%:E ->
    ((factor^-1)%R)%:E*psi (val j)<=metric_real_diameter_cost a p (val j).
  move=> hj; have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  case he: (extended_metric_diameter (val j)) h0 hj=> [d| |] h0 hj; last 2 first.
  + by rewrite leye_eq in hj.
  + by [].
  have hd : (0<=d)%R by move: h0; rewrite lee_fin.
  have hdt : (d+d<t)%R.
    have hh : (d<=t/4)%R by move: hj; rewrite lee_fin.
    have h4 : (0<(4:R))%R by rewrite ltr0n.
    have htt : (t/4+t/4<t)%R.
      have hq : (t/4*4=t)%R by rewrite divfK ?pnatr_eq0.
      lra.
    lra.
  have hdi : extended_metric_diameter (val j)<=d%:E by rewrite he.
  have hb := @spherical_metric_real_power_scale_bound R X a p ha hp psi (val j) d t hpsi (set_valP j) hd hdt hdi.
  rewrite (metric_real_power_cost_double a p hd) in hb.
  have hh := lee_wpmul2l hciE hb.
  rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hh.
  by rewrite /metric_real_diameter_cost he.
have hb := @measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) ((t/4)%R%:E)
  phi (fun B => ((factor^-1)%R)%:E*psi B) hphi (finite_scale_is_measure hpsi_measure hci) hgen A.
have hup : phi A<=@metric_real_power_measure R X a p A.
  apply: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) _ hm A ((t/4)%R%:E) phi _ hphi).
  by rewrite lte_fin divr_gt0 // ltr0n.
have hh := lee_wpmul2l hcE (le_trans hb hup).
rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in hh.
apply: le_trans _ hh.
exact (@metric_scale_envelope_antitone_cutoff R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) t%:E tau psi xi hpsi hxi hnt A).
Qed.
