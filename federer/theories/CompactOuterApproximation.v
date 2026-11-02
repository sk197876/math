(** Federer (1969), 2.10.22, p. 186: choose compact S_k whose interiors
    contain D_k and whose diameters and costs remain small. The supporting
    existence proof uses closed sublevels of the already sealed distance
    profile and Hausdorff continuity of the cost. Bounded compactness makes
    these neighbourhoods compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded CompactProfileNearest
  MetricClosedBalls MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceContinuity
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance HausdorffDiameter
  LipschitzFunctionCompact RealMetricBackground CompactGeneratorCostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_positive_neighborhood_exists]: supporting
    compact neighbourhood S_k in 2.10.22,
    p. 186. Every positive radius gives a compact
    neighbourhood of C within that Hausdorff error. *)
Lemma compact_positive_neighborhood_exists (R : realType) (X : metricType R)
    (C : compact_metric_set X) (t : R) :
  metric_boundedly_compact X -> 0<t ->
  exists D : compact_metric_set X, val C `<=` interior (val D) /\ hausdorff_distance C D<=t.
Proof.
move=> hX ht.
pose A : set X := [set x | compact_set_distance_profile C x<=t].
have hprof := compact_set_distance_profile_specification C.
have hclosed : closed A.
  apply: (@preimage_closed X (real_line_metric R) (compact_set_distance_profile C) [set u | u<=t]).
  - move=> x hx; exact: metric_set_distance_continuous hprof x.
  - exact: closed_le.
have [a ha] := (set_valP C).2.
have [r [hr hball]] := compact_metric_set_ball_bound C a.
have hrt : 0<=r+t := addr_ge0 (ltW hr) (ltW ht).
have hcompact : compact A.
  apply: (subclosed_compact hclosed (hX a (r+t) hrt))=> x hx.
  have [c [hc hxc]] := compact_profile_nearest_point C x.
  have hca : mdist a c<=r := hball c hc.
  have htri := metric_triangle a c x.
  rewrite (metric_sym c x) hxc in htri.
  change (is_true (mdist a x<=r+t)); change (is_true (compact_set_distance_profile C x<=t)) in hx; lra.
have hCA : val C `<=` A.
  move=> x hx; have hz := proj2 (compact_set_distance_profile_zero C x) hx.
  change (is_true (compact_set_distance_profile C x<=t)); by rewrite hz; exact: ltW ht.
have hne : A !=set0 by exists a; exact: hCA a ha.
pose D : compact_metric_set X := exist _ A (mem_set (conj hcompact hne)).
exists D; split.
- pose U : set X := [set x | compact_set_distance_profile C x<t].
  have hU : open U.
    apply: (@open_comp X (real_line_metric R) (compact_set_distance_profile C) [set u | u<t]).
    + move=> x hx; exact: metric_set_distance_continuous hprof x.
    + exact: open_lt.
  move=> x hx.
  have hUx : U x.
    have hz := proj2 (compact_set_distance_profile_zero C x) hx.
    by rewrite /U /= hz.
  have hnear : nbhs x U by rewrite openE in hU; exact: hU x hUx.
  apply: (filterS _ hnear)=> y hy; exact: ltW hy.
- apply: (proj2 (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) C D (ltW ht))).
  split=> x hx.
  + have hz := proj2 (compact_set_distance_profile_zero D x) (hCA x hx).
    by rewrite hz; exact: ltW ht.
  + exact hx.
Qed.

(** Source for [compact_cost_open_refinement]: direct
    neighbourhood selection used for S_k in the proof
    of 2.10.22, p. 186. Strict diameter and
    cost margins allow an interior-containing compact
    enlargement with both strict bounds preserved. *)
Theorem compact_cost_open_refinement (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost)
    (C : compact_metric_set X) (delta b : R) :
  metric_boundedly_compact X -> compact_metric_diameter C<delta -> cost C<b ->
  exists D : compact_metric_set X, val C `<=` interior (val D) /\
    compact_metric_diameter D<delta /\ cost D<b.
Proof.
move=> hX hdiam hcost.
have hO : nbhs (cost C : real_line_metric R) [set u | u<b].
  have ho : @open (real_line_metric R) [set u | u<b] := @open_lt R b.
  rewrite openE in ho; exact: ho (cost C) hcost.
have hnear : nbhs (C : compact_hausdorff_space X) [set D | cost D<b] :=
  @compact_cost_continuous_law R X cost hc C _ hO.
have [e he hbound] := (metricType_numDomainType.nbhs_mdistP (C : compact_hausdorff_space X) _).1 hnear.
pose t := Order.min (e/2) ((delta-compact_metric_diameter C)/4).
have ht : 0<t by rewrite /t lt_min !divr_gt0 ?ltr0n // subr_gt0.
have hte : t<=e/2 by rewrite /t ge_min lexx.
have htd : t<e.
  apply: le_lt_trans hte _; by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
have htm : t<=(delta-compact_metric_diameter C)/4 by rewrite /t ge_min lexx orbT.
have [D [hCD hd]] := compact_positive_neighborhood_exists C hX ht.
exists D; split=> //; split.
- have hdc := hausdorff_diameter_one_sided_bound D C.
  rewrite (hausdorff_distance_symmetric_law (@hausdorff_distance_specification R X) D C) in hdc.
  have htwo : (0<=2 :> R) by rewrite ler0n.
  have hmul := ler_wpM2l htwo hd; lra.
- apply: hbound; change (is_true (hausdorff_distance C D<e)).
  exact: le_lt_trans hd htd.
Qed.
