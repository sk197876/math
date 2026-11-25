(** Federer (1969), 2.9.14, p. 159: openness of the locus where one
    closed-ball measure strictly exceeds another for an allowed radius. The
    proof uses monotonicity, continuity from above in 2.1.3(5), p. 55, and
    the metric triangle inequality. no separate item there states this
    ball-comparison lemma. The working erratum has no correction to 2.9.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
(** The narrow [lra] import checks only finite real-field arithmetic
    in the radius choice; it supplies no measure or topology theorem. *)
From Federer Require Import RealMetricBackground MetricClosedBalls CoveringFamilyUP
  MeasureUP MeasureBasic MeasureDerivationContext ClosedBallMeasureContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [ball_measure_comparison_points]: direct set
    in Federer 2.9.14, p. 159. Both measures evaluate
    closed balls, and a radius belongs to the given real
    open set J. No finiteness or regularity of alpha is
    included in this set definition. *)
Definition ball_measure_comparison_points (R : realType) (X : metricType R)
    (alpha beta : set X -> \bar R) (J : set (real_line_metric R)) : set X :=
  [set x | exists r : R, J r /\ beta (metric_closed_ball x r)<alpha (metric_closed_ball x r)].

(** Source for [ball_measure_comparison_stable_radius]: direct
    radius perturbation in the proof of Federer 2.9.14,
    p. 159. Choose epsilon with r+epsilon in J and
    beta B(a,r+2epsilon)<alpha B(a,r). The two triangle-
    inequality ball inclusions then preserve strict comparison
    at every point of the epsilon neighbourhood of a. *)
Lemma ball_measure_comparison_stable_radius (R : realType) (X : metricType R)
    (alpha beta : set X -> \bar R) (J : set (real_line_metric R)) (a : X) (r : R) :
  is_measure alpha -> is_derivation_measure beta -> open J -> J r -> (0<r)%R ->
  beta (metric_closed_ball a r)<alpha (metric_closed_ball a r) ->
  exists e : R, (0<e)%R /\ J (r+e)%R /\ forall x, (mdist a x<e)%R ->
    beta (metric_closed_ball x (r+e)%R)<alpha (metric_closed_ball x (r+e)%R).
Proof.
move=> halpha hbeta hJ hJr hr hcmp.
have hnb : nbhs (r : real_line_metric R) J by rewrite openE in hJ; exact: hJ r hJr.
have [t ht hJt] := (metricType_numDomainType.nbhs_mdistP (r : real_line_metric R) _).1 hnb.
have [d [hd hmass]] := @closed_ball_mass_right_neighbourhood R X beta a r
  (alpha (metric_closed_ball a r)) hbeta (ltW hr) hcmp.
pose e := (Num.min (d/4) (t/2))%R.
have hd4 : (0<d/4)%R by rewrite divr_gt0 // ltr0n.
have ht2 : (0<t/2)%R by rewrite divr_gt0 // ltr0n.
have he : (0<e)%R by rewrite /e lt_min hd4 ht2.
have hed : (e<=d/4)%R by rewrite /e ge_min lexx.
have het : (e<=t/2)%R by rewrite /e ge_min lexx orbT.
have hsmall : (e<t)%R by lra.
have h2e : (e+e<=d)%R by lra.
exists e; split=> //; split.
- apply: hJt.
  have hdist : mdist (r : real_line_metric R) (r+e)%R=e.
    rewrite real_line_metric_distanceE opprD addrA subrr add0r normrN.
    by rewrite (ger0_norm (ltW he)).
  by rewrite /= hdist.
- move=> x hx.
  have ha : metric_closed_ball a r `<=` metric_closed_ball x (r+e)%R.
    move=> z hz; have htri := metric_triangle x a z.
    rewrite (metric_sym x a) in htri.
    have hh := lerD (ltW hx) hz.
    rewrite [(e+r)%R]addrC in hh; exact: le_trans htri hh.
  have hb : metric_closed_ball x (r+e)%R `<=` metric_closed_ball a (r+d)%R.
    move=> z hz; have htri := metric_triangle a x z.
    have hh := le_trans htri (lerD (ltW hx) hz).
    apply: le_trans hh _; by lra.
  have hbetale := @measure_mono R X beta (derivation_measure_law hbeta) _ _ hb.
  have halphale := @measure_mono R X alpha halpha _ _ ha.
  exact: le_lt_trans hbetale (lt_le_trans hmass halphale).
Qed.

(** Source for [federer_2_9_14]: complete assertion of Federer
    2.9.14, p. 159. The allowed radii form an open subset
    of the positive real line. Alpha is any measure, whereas
    beta is in the original class M. In particular, alpha
    need not have finite values on bounded sets. *)
Theorem federer_2_9_14 (R : realType) (X : metricType R)
    (alpha beta : set X -> \bar R) (J : set (real_line_metric R)) :
  is_measure alpha -> is_derivation_measure beta -> open J ->
  (forall r, J r -> (0<r)%R) -> open (ball_measure_comparison_points alpha beta J).
Proof.
move=> halpha hbeta hJ hpos; rewrite openE=> a [r [hJr hcmp]].
have [e [he [hJe hstable]]] := @ball_measure_comparison_stable_radius R X alpha beta J a r
  halpha hbeta hJ hJr (hpos r hJr) hcmp.
apply: (metricType_numDomainType.nbhs_mdistP a _).2.
exists e=> // x hx; exists (r+e)%R; split=> //; exact: hstable x hx.
Qed.
