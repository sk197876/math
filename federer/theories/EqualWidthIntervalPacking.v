(** Federer (1969), 2.10.29, p. 194, first case: a test interval of length
    at most sigma_(j-1) meets at most two disjoint level intervals of that
    same positive length. Count endpoint intersections too. The proof uses
    their centres and the elementary three-point packing contradiction,
    without an order imposed on the finite family. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  CompactIntervalGaugeGeometry FiniteNoThreeCardinality ThreePointRealPacking.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_width_interval_meeting_count]: direct
    at-most-two assertion in the first case
    of 2.10.29, p. 194. The family is
    finite and disjoint, its members have the
    common positive actual diameter r, and
    the test interval has diameter at most r. *)
Theorem equal_width_interval_meeting_count (R : realType) (H : {fset compact_real_intervals R})
    (T : compact_real_intervals R) (r : R) :
  0<r ->
  (forall S, S \in H -> fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=r) ->
  (forall S U, S \in H -> U \in H -> S!=U -> val S `&` val U=set0) ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))<=r ->
  (#|` [fset S in H | `[< val T `&` val S !=set0 >]]|<=2)%N.
Proof.
move=> hr hwidth hdisjoint htest.
pose I := compact_real_intervals R.
have hex (S : I) : exists ab : R*R,
    ab.1<=ab.2 /\ val S=(`[ab.1,ab.2] : set (real_line_metric R)).
  have [a [b [hab hS]]] := set_valP S; exists (a,b); by split.
pose l (S : I) := (projT1 (cid (hex S))).1.
pose u (S : I) := (projT1 (cid (hex S))).2.
have hends (S : I) : l S<=u S /\ val S=(`[l S,u S] : set (real_line_metric R)) := projT2 (cid (hex S)).
have hlen (S : I) : S \in H -> u S-l S=r.
  move=> hS; have hh := hwidth S hS.
  by rewrite (hends S).2 (extended_metric_diameter_segment (hends S).1) in hh.
pose mid (S : I) := l S+r/2.
have hseparated (S U : I) : S \in H -> U \in H -> S!=U -> r<`|mid S-mid U|.
  move=> hS hU hne; have hd := hdisjoint S U hS hU hne.
  rewrite (hends S).2 (hends U).2 in hd.
  have hcases := (@compact_segments_disjoint_endpoints R (l S) (u S) (l U) (u U)
    (hends S).1 (hends U).1).1 hd.
  have hLS := hlen S hS; have hLU := hlen U hU.
  rewrite /mid ltr_normr; case: hcases=> [hSU|hUS]; apply/orP; [right|left]; lra.
have [a [b [hab hT]]] := set_valP T.
have htestlen : b-a<=r by move: htest; rewrite hT (extended_metric_diameter_segment hab).
have hcentre (S : I) : S \in H -> val T `&` val S !=set0 ->
    a-r/2<=mid S /\ mid S<=b+r/2.
  move=> hS [x [hxT hxS]].
  have /andP[hax hxb] : a<=x<=b by move: hxT; rewrite hT /= in_itv.
  have /andP[hlx hxu] : l S<=x<=u S by move: hxS; rewrite (hends S).2 /= in_itv.
  have hLS := hlen S hS; rewrite /mid; split; lra.
apply: finite_family_no_three_cardinality=> S U V.
rewrite !in_fset /= => /andP[hS /asboolP hxS] /andP[hU /asboolP hxU] /andP[hV /asboolP hxV] hSU hSV hUV.
have [hSl hSu] := hcentre S hS hxS.
have [hUl hUu] := hcentre U hU hxU.
have [hVl hVu] := hcentre V hV hxV.
have hspan : (b+r/2)-(a-r/2)<=2*r by lra.
exact (@three_real_points_separated_short_interval R (a-r/2) (b+r/2) r (mid S) (mid U) (mid V)
  hSl hSu hUl hUu hVl hVu hspan (hseparated S U hS hU hSU)
  (hseparated S V hS hV hSV) (hseparated U V hU hV hUV)).
Qed.
