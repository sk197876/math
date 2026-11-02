(** Federer (1969), 2.10.21, p. 183: the profile image Omega(F_(a,r)) is
    closed. Follow the printed sublevel-set argument. A closure profile is
    the distance to its nonempty compact zero set; decreasing positive
    sublevels eventually lie near that zero set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricSetDistanceUP MetricSetDistanceBasic
  MetricSetDistanceContinuity CompactBallProfiles CompactProfileSublevels CompactSetDistanceProfile
  LipschitzUP LipschitzFunctionCompact CompactDecreasingNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_ball_profiles_closed]: direct
    closedness of Omega(F_(a,r)) in 2.10.21,
    p. 183. The supporting statement includes radius
    zero; the book only needs positive radius. *)
Theorem compact_ball_profiles_closed (R : realType) (X : metricType R) (a : X) (r : R) :
  metric_boundedly_compact X -> 0<=r -> closed (compact_ball_profiles a r).
Proof.
move=> hX hr f hf.
have [hc [hn hball]] := closure_profile_zero_set_compact_nonempty hX hr hf.
pose D : compact_metric_set X := exist _ [set x | f x=0] (mem_set (conj hc hn)).
have hD : compact_sets_in_ball a r D := hball.
have hLip := (compact_ball_profile_closure_laws hf).1.
have hspec := compact_set_distance_profile_specification D.
have hlower x : f x<=compact_set_distance_profile D x.
  apply: (@metric_set_distance_greatest R X (val D) (compact_set_distance_profile D) hspec x (f x))=> y hy.
  have hz : f y=0 := hy.
  have hh := hLip.2 x y I I.
  rewrite real_line_metric_distanceE hz subr0 mul1r in hh.
  exact: le_trans (ler_norm _) hh.
have hupper x : compact_set_distance_profile D x<=f x.
  case: (leP (compact_set_distance_profile D x) (f x))=> // hgt.
  pose delta := (compact_set_distance_profile D x-f x)/3.
  have hd : 0<delta by rewrite /delta divr_gt0 // subr_gt0.
  pose V : set X := [set y | compact_set_distance_profile D y<delta].
  have hV : open V.
    apply: (@open_comp X (real_line_metric R) (compact_set_distance_profile D) [set y | y<delta]).
    - move=> y hy; exact: metric_set_distance_continuous hspec y.
    - exact: open_lt.
  pose C (n : nat) : set X := [set y | f y<=n.+1%:R^-1].
  have hp n : (0<n.+1%:R^-1 :> R) by rewrite invr_gt0 ltr0n.
  have hclosed n : closed (C n) := @closure_profile_sublevel_closed R X a r f n.+1%:R^-1 hf.
  have hdec n m (hnm : (n<=m)%N) : C m `<=` C n.
    move=> y hy; apply: le_trans hy _.
    have hn0 : (0<n.+1%:R :> R) by rewrite ltr0n.
  have hm0 : (0<m.+1%:R :> R) by rewrite ltr0n.
  have hcast : (n.+1%:R<=m.+1%:R :> R) by rewrite ler_nat.
  by rewrite (lef_pV2 hm0 hn0).
  have hK : (\bigcap_n C n) `<=` V.
    move=> y hy.
    have hzero : [set z | f z=0] y.
      have he := closure_profile_reciprocal_intersection hf; rewrite -he; exact hy.
    have hz := proj2 (compact_set_distance_profile_zero D y) hzero.
    by rewrite /V /= hz.
  have hC0 : compact (C 0%N) := closure_profile_sublevel_compact hX hr (ltW (hp 0%N)) hf.
  have [N hN] := @compact_decreasing_eventually_in_open X C V hC0 hclosed hdec hV hK.
  pose e := Order.min (N.+1%:R^-1) delta.
  have he : 0<e by rewrite /e lt_min (hp N) hd.
  have heN : e<=N.+1%:R^-1 by rewrite /e ge_min lexx.
  have heD : e<=delta by rewrite /e ge_min lexx orbT.
  have hcompact : compact (metric_closed_ball a r `|` [set x]) := compactU (hX a r hr) (@compact_set1 X x).
  have [E [hE happrox]] := compact_ball_profile_closure_approximation hf hcompact he.
  have hEd y (hy : val E y) : compact_set_distance_profile D y<=delta.
    have hh := happrox y (or_introl (hE y hy)).
    have hz := proj2 (compact_set_distance_profile_zero E y) hy.
    rewrite hz subr0 in hh.
    have hfy : f y<=N.+1%:R^-1 := le_trans (le_trans (ler_norm _) (ltW hh)) heN.
    exact: ltW (hN N (leqnn N) y hfy).
  have hdiff := (proj2 (compact_distance_profile_signed_bound E D delta) hEd) x.
  have hx := happrox x (or_intror erefl).
  have hneg := ler_norm (compact_set_distance_profile E x-f x).
  rewrite -opprB normrN in hneg.
  have hval := le_lt_trans hneg hx.
  have hvalD := lt_le_trans hval heD.
  rewrite /delta in hdiff hvalD; lra.
have heq : f=compact_set_distance_profile D.
  apply: funext=> x; apply/eqP; by rewrite eq_le (hlower x) (hupper x).
exists D; by split.
Qed.
