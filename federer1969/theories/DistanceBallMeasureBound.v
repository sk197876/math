(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls MetricSetDistanceUP
  HalfDistanceBallGeometry UniformBallGrowthAdequacy ClosedBallRatioBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [distance_ball_fivefold_measure_bound]: direct
    chain of ball-measure inequalities in Federer 2.9.17,
    p. 162, from psi B(y,5s) through a nearby z
    in C_n to c lambda^2 phi B(y,s). Radii 8s,
    11s and two applications of fivefold growth follow the
    printed proof. The numerator has only measure laws;
    no local finiteness or Borel regularity is added. *)
Lemma distance_ball_fivefold_measure_bound (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (A : set X) (d : X -> R)
    (hd : is_metric_set_distance A d) (c delta lambda mu : R) (x y : X) (r : R) :
  is_measure phi -> is_measure psi -> closed A -> (0<=c)%R -> (0<lambda)%R ->
  has_uniform_fivefold_ball_growth phi setT mu lambda ->
  (forall z, A z -> bounded_centered_ball_ratio_locus psi phi c delta z) ->
  A x -> ~ A y -> (0<r)%R -> metric_closed_ball x r y ->
  (r<delta/4)%R -> (r<mu/4)%R ->
  let s := (d y/2)%R in
  psi (metric_closed_ball y (5*s)%R)<=((c*lambda^+2)%R)%:E*phi (metric_closed_ball y s).
Proof.
move=> hphi hpsi hA hc hl hg hbound hx hy hr hxy hrd hrm.
pose s := (d y/2)%R.
change (psi (metric_closed_ball y (5*s)%R)<=
  ((c*lambda^+2)%R)%:E*phi (metric_closed_ball y s)).
have [hs [hsr [_ [z [hz hzy]]]]] :=
  @half_distance_ball_geometry R X A d hd x y r hA hx hy hr hxy.
change (is_true (0<s)%R) in hs.
change (is_true (s<=r/2)%R) in hsr.
change (is_true (mdist y z<3*s)%R) in hzy.
have h8pos : (0<8*s)%R by rewrite mulr_gt0 // ltr0n.
have h8delta : (8*s<delta)%R by lra.
have hs_mu : (s<mu)%R by lra.
have h5pos : (0<5*s)%R by rewrite mulr_gt0 // ltr0n.
have h5mu : (5*s<mu)%R by lra.
have hsub58 : metric_closed_ball y (5*s)%R `<=` metric_closed_ball z (8*s)%R.
  move=> t ht; apply: le_trans (metric_triangle z y t) _.
  rewrite (metric_sym z y); have hb := lerD (ltW hzy) ht; apply: le_trans hb _; lra.
have hsub811 : metric_closed_ball z (8*s)%R `<=` metric_closed_ball y (11*s)%R.
  move=> t ht; apply: le_trans (metric_triangle y z t) _.
  have hb := lerD (ltW hzy) ht; apply: le_trans hb _; lra.
have hsub1125 : metric_closed_ball y (11*s)%R `<=` metric_closed_ball y (25*s)%R.
  move=> t ht; apply: le_trans ht _; lra.
have h25 : phi (metric_closed_ball y (25*s)%R)<=
    lambda%:E*phi (metric_closed_ball y (5*s)%R).
  have h := hg y I (5*s)%R h5pos h5mu.
  have he : (5*(5*s)= 25*s)%R by lra.
  by rewrite he in h; exact: ltW h.
have h5 := ltW (hg y I s hs hs_mu).
have hl0 : 0<=lambda%:E by rewrite lee_fin; exact: ltW hl.
have hc0 : 0<=c%:E by rewrite lee_fin.
have hlast := @lee_wpmul2l R lambda%:E hl0 _ _ h5.
have hphi8 := le_trans (@measure_mono R X phi hphi _ _ hsub811)
  (le_trans (@measure_mono R X phi hphi _ _ hsub1125) (le_trans h25 hlast)).
have hmass := le_trans (@measure_mono R X psi hpsi _ _ hsub58)
  (le_trans (hbound z hz (8*s)%R h8pos h8delta)
    (@lee_wpmul2l R c%:E hc0 _ _ hphi8)).
by move: hmass; rewrite !muleA -!EFinM expr2 mulrA.
Qed.
