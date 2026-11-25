(** Attainment of the class radius in Federer (1969), 2.10.31, p. 195.
    Intersect the nonempty Hausdorff-closed class with a compact
    containing-ball family from 2.10.21, then minimise the continuous least
    enclosing radius. Every smaller-radius competitor lies in that same
    compact part of the class. This expands the printed compactness argument
    without assuming attainment of an arbitrary set-theoretic infimum.
    Source context: CompactEnclosingRadiusUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactSetDistanceProfile
  CompactHausdorffMetric CompactBallProfiles CompactHausdorffBall LipschitzFunctionCompact
  CompactMaximum CompactEnclosingRadius CompactEnclosingRadiusHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_compact_family_minimum_radius]: supporting
    attained minimal radius in the first paragraph
    of the proof of 2.10.31, p. 195.
    This metric statement precedes the use of
    Steiner stability and works about any fixed centre. *)
Theorem closed_compact_family_minimum_radius (R : realType) (X : metricType R)
    (a : X) (C : set (compact_hausdorff_space X)) :
  metric_boundedly_compact X -> C !=set0 -> closed C ->
  exists S : compact_hausdorff_space X, C S /\
    forall T : compact_hausdorff_space X, C T -> compact_enclosing_radius a S<=compact_enclosing_radius a T.
Proof.
move=> hX [S0 hS0] hCc.
pose r0 := compact_enclosing_radius a S0.
pose r := r0+1.
have hr0 : 0<=r0 := compact_enclosing_radius_nonnegative a S0.
have hr : 0<=r by rewrite /r; lra.
pose F : set (compact_hausdorff_space X) := [set S | compact_sets_in_ball a r S].
have hFc : compact F := compact_hausdorff_ball_compact hX hr.
have hFclosed : closed F := compact_closed (@metric_hausdorff R (compact_hausdorff_space X)) hFc.
pose K := C `&` F.
have hKc : compact K.
  apply: (subclosed_compact (closedI hCc hFclosed) hFc)=> S [_ hS]; exact hS.
have hK0 : K S0.
  split=> // x hx.
  have hh := compact_enclosing_radius_contains a S0 x hx.
  change (is_true (mdist a x<=r)); change (is_true (mdist a x<=r0)) in hh.
  rewrite /r; lra.
have hKne : K !=set0 by exists S0.
have hc := @compact_enclosing_radius_continuous R X a.
have hn : continuous (fun S : compact_hausdorff_space X=>(-compact_enclosing_radius a S : R^o)).
  move=> S; exact (@continuousN R R^o [the topologicalType of compact_hausdorff_space X]
    (fun T=>compact_enclosing_radius a T) S (hc S)).
have [S [hS hmin]] := continuous_compact_maximum hKne hKc hn.
have hSr : compact_enclosing_radius a S<=r.
  exact (compact_enclosing_radius_least a S hr hS.2).
exists S; split; first exact hS.1.
move=> T hT; case: (leP (compact_enclosing_radius a T) r)=> hTr.
- have hKT : K T.
    split=> // x hx.
    have hh := compact_enclosing_radius_contains a T x hx.
    change (is_true (mdist a x<=r)); exact: le_trans hh hTr.
  have hh := hmin T hKT; by rewrite lerN2 in hh.
- exact: le_trans hSr (ltW hTr).
Qed.
