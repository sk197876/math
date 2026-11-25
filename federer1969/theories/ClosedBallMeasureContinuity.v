(** Federer (1969), 2.9.14, p. 159: openness of the locus where one
    closed-ball measure strictly exceeds another for an allowed radius. The
    proof uses monotonicity, continuity from above in 2.1.3(5), p. 55, and
    the metric triangle inequality. no separate item there states this
    ball-comparison lemma. The working erratum has no correction to 2.9.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureDerivationContext BorelRegularMeasureUP
  MetricClosedBalls TopologicalBorel CoveringFamilyLaws MeasureContinuityAbove
  ExtendedRealOrderLimit ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [closed_ball_reciprocal_intersection]: supporting
    decreasing intersection in the proof of Federer 2.9.14,
    p. 159. Balls of radii r+1/(n+1) decrease to the
    closed ball of radius r, directly from the metric order. *)
Lemma closed_ball_reciprocal_intersection (R : realType) (X : metricType R)
    (a : X) (r : R) :
  (\bigcap_n metric_closed_ball a (r+((n.+1%:R : R)^-1))%R)=metric_closed_ball a r.
Proof.
apply/seteqP; split=> x.
- move=> hx; rewrite /metric_closed_ball /= -lee_fin.
  apply: (@extended_real_reciprocal_upper_bound R (mdist a x)%:E r)=> n.
  rewrite lee_fin; exact: hx n Logic.I.
- move=> hx n _; apply: le_trans hx _.
  by rewrite lerDl invr_ge0 ler0n.
Qed.

(** Source for [closed_ball_measure_right_limit]: supporting
    right continuity in the radius used in Federer 2.9.14,
    p. 159. Closed balls are measurable and the first
    enlarged ball is bounded, so 2.1.3(5), p. 55,
    applies with finite first measure. No properness or local
    compactness of the metric space is assumed. *)
Theorem closed_ball_measure_right_limit (R : realType) (X : metricType R)
    (beta : set X -> \bar R) (a : X) (r : R) :
  is_derivation_measure beta -> (0<=r)%R ->
  extended_decreases_to
    (fun n => beta (metric_closed_ball a (r+((n.+1%:R : R)^-1))%R))
    (beta (metric_closed_ball a r)).
Proof.
move=> hbeta hr; have hm := derivation_measure_law hbeta.
pose F n := metric_closed_ball a (r+((n.+1%:R : R)^-1))%R.
have hFm n : measure_measurable beta (F n).
  apply: (@borel_regular_borel_measurable R X beta hm
    (derivation_measure_borel_regular hbeta)).
  apply: closed_borel_set; exact: metric_closed_ball_closed.
have hmono n m : (n<=m)%N -> F m `<=` F n.
  move=> hnm x hx; apply: le_trans hx _; rewrite lerD2l.
  have hn : (0<(n.+1%:R : R))%R by rewrite ltr0n.
  have hmp : (0<(m.+1%:R : R))%R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hmp hn) ler_nat.
have hfin : beta (F 0%N)< +oo.
  apply: derivation_measure_bounded_finite hbeta _ _.
  apply: covering_closed_ball_bounded; apply: addr_ge0 hr _.
  by rewrite invr_ge0 ler0n.
have hl := @measure_continuity_above R X beta hm F hFm hmono hfin.
by rewrite /F closed_ball_reciprocal_intersection in hl.
Qed.

(** Source for [closed_ball_mass_right_neighbourhood]: the
    measure inequality on the enlarged ball in Federer 2.9.14,
    p. 159, first proof sentence, before choosing epsilon.
    Any strict upper bound on beta B(a,r) remains an upper
    bound after a sufficiently small positive radius increase;
    the upper bound may itself be infinite. *)
Lemma closed_ball_mass_right_neighbourhood (R : realType) (X : metricType R)
    (beta : set X -> \bar R) (a : X) (r : R) (c : \bar R) :
  is_derivation_measure beta -> (0<=r)%R -> beta (metric_closed_ball a r)<c ->
  exists d : R, (0<d)%R /\ beta (metric_closed_ball a (r+d)%R)<c.
Proof.
move=> hbeta hr hc.
have hlim := (@closed_ball_measure_right_limit R X beta a r hbeta hr).
have [n hn] := hlim.2.2 c hc.
exists ((n.+1%:R : R)^-1)%R; split; first by rewrite invr_gt0 ltr0n.
exact: hn n (leqnn n).
Qed.
