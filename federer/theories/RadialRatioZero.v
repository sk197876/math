(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext MeasureDerivates
  DerivationRatioDomain PartialFunctionUP MetricClosedBalls CenteredBallRatioDomain NullBallLocus
  RadialBallRatios ExtendedRealBounds ExtendedRealReciprocalBounds PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [centered_ball_ratio_upper_limit_nonnegative]:
    supporting sign for the zero-or-infinite alternative in
    Federer 2.9.17, p. 162. Every actual measure
    ratio is nonnegative, and every positive radius cutoff
    contains an actual quotient outside the null-ball locus. *)
Lemma centered_ball_ratio_upper_limit_nonnegative (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> is_measure psi -> ~ measure_null_ball_points phi x ->
  0<=centered_ball_ratio_upper_limit psi phi x.
Proof.
move=> hphi hpsi hn.
apply: extended_real_inf_greatest=> b [d [hd ->]].
pose r := (d/2)%R.
have hr : (0<r)%R by rewrite /r divr_gt0 // ltr0n.
have hrd : (r<d)%R by rewrite /r ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have hq := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
have hnon := @measure_ratio_nonnegative R X psi phi (metric_closed_ball x r)
  (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)) hpsi (derivation_measure_law hphi) hq.
apply: le_trans hnon (extended_real_sup_upper _).
by exists r; split=> //; split.
Qed.

(** Source for [centered_ball_ratio_upper_limit_zero]: supporting
    zero upper-limit conclusion for points of C_n in
    Federer 2.9.17, p. 162. Arbitrarily small
    positive scalar upper bounds and quotient nonnegativity force
    the literal radial limsup to be zero. *)
Lemma centered_ball_ratio_upper_limit_zero (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> is_measure psi -> ~ measure_null_ball_points phi x ->
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall r, (0<r)%R -> (r<d)%R ->
      psi (metric_closed_ball x r)/phi (metric_closed_ball x r)<e%:E) ->
  centered_ball_ratio_upper_limit psi phi x=0.
Proof.
move=> hphi hpsi hn hsmall; apply/eqP.
rewrite eq_le (@centered_ball_ratio_upper_limit_nonnegative R X psi phi x hphi hpsi hn) andbT.
apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=> n; rewrite add0r.
have hp : (0<(((n.+1)%:R : R)^-1))%R by rewrite invr_gt0 ltr0n.
have [d [hd hb]] := hsmall _ hp.
have hlev : centered_ball_ratio_upper_limit psi phi x<=
    extended_real_sup (centered_ball_ratio_values psi phi x d).
  apply: extended_real_inf_lower; by exists d.
apply: le_trans hlev _; apply: extended_real_sup_least=> y [r [hr [hrd hy]]].
have hq := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
have heq := partial_function_single_valued hy hq.
rewrite heq; exact: ltW (hb r hr hrd).
Qed.

(** Source for [nonnegative_positive_right_limit_zero]: supporting
    ordinary zero radius limit in the proof of Federer
    2.9.17, p. 162. A nonnegative function
    eventually below every positive real epsilon converges to
    zero in the existing extended-real order-limit specification. *)
Lemma nonnegative_positive_right_limit_zero (R : realType) (u : R -> \bar R) :
  (forall r, (0<r)%R -> 0<=u r) ->
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall r, (0<r)%R -> (r<d)%R -> u r<e%:E) ->
  positive_right_extended_order_limit u 0.
Proof.
move=> hn hs; split.
- move=> a ha; exists 1%R; split; first exact: ltr01.
  move=> r hr _; exact: lt_le_trans ha (hn r hr).
- move=> b; case: b=> [b| |] hb.
  + have hp : (0<b)%R by move: hb; rewrite lte_fin.
    exact: hs b hp.
  + have [d [hd hsmall]] := hs 1%R (ltr01).
    exists d; split=> // r hr hrd; exact: lt_trans (hsmall r hr hrd) (ltry 1%R).
  + by move: hb; rewrite ltNge leNye.
Qed.
