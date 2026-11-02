(** Federer (1969), 2.10.22, pp. 184–186: continuity below of every finite
    strictly positive cutoff approximation on arbitrary increasing targets.
    The family is exactly all nonempty compact sets, with finite nonnegative
    Hausdorff-continuous costs positive on positive diameters. First use the
    bounded-target compact-cover proof, then the radial exhaustion of
    2.10.20, pp. 181–182. The resulting common-bound characterization
    identifies the actual increasing order limit. no identical compact-cost
    continuity theorem was located. The working erratum contains no
    correction to 2.10.22. Detailed proof-route expansions:
    CompactCostBoundedContinuity.v and its imports. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactGeneratorCostUP CompactCostBoundedContinuity
  MetricClosedBalls MetricScaleEnvelopeUP MetricScaleCutoffCost MeasureUP MeasureBasic
  RadialScaleContinuity RadialMassSupremum ExtendedRealOrderLimit ExtendedRealBoundsUP
  LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_continuity_common_bound]: supporting
    removal of the bounded-target reduction in
    2.10.22, pp. 184–186, using 2.10.20.
    The ambient space and the union may be empty;
    no chosen centre is required in the statement. *)
Theorem compact_cost_continuity_common_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta : R) (nu : set X -> \bar R) (A : nat -> set X) (s : R) :
  metric_boundedly_compact X -> 0<delta -> 0<=s ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  (forall i j, (i<=j)%N -> A i `<=` A j) ->
  (forall j, (nu (A j)<=s%:E)%E) -> (nu (\bigcup_j A j)<=s%:E)%E.
Proof.
move=> hX hd hs hn hinc hbound.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := metric_scale_envelope_is_measure hn hc0.
pose B := \bigcup_j A j.
change (nu B<=s%:E)%E.
case: (pselect (B !=set0))=> [[a ha]|hBempty].
- have hradial := @metric_scale_radial_continuity R X (compact_metric_set X)
    (fun C=>val C) (fun C=>(c C)%:E) delta nu B a hd hc0 hn.
  have hball r : (nu (B `&` metric_closed_ball a r)<=s%:E)%E.
    pose C j := A j `&` metric_closed_ball a r.
    pose t := Order.max r 0.
    have ht : 0<=t by rewrite /t le_max lexx orbT.
    have hrt : r<=t by rewrite /t le_max lexx.
    have hCinc i j (hij : (i<=j)%N) : C i `<=` C j.
      move=> x [hx hxr]; split=> //; exact: hinc i j hij x hx.
    have hCball j : C j `<=` metric_closed_ball a t.
      move=> x [_ hxr]; exact: le_trans hxr hrt.
    have hCbound j : (nu (C j)<=s%:E)%E.
      apply: le_trans _ (hbound j); apply: (@measure_mono R X nu hm)=> x [hx _]; exact hx.
    have hh := @compact_cost_bounded_continuity_bound R X c hc delta nu C a t s
      hX hd ht hs hn hCinc hCball hCbound.
    have heq : (\bigcup_j C j)=B `&` metric_closed_ball a r.
      apply/seteqP; split.
      - move=> x [j _ [hx hxr]]; split=> //; by exists j.
      - move=> x [[j _ hx] hxr]; exists j=> //; by split.
    by rewrite heq in hh.
  rewrite leNgt; apply/negP=> hbad.
  have [r hr] := hradial.1 s%:E hbad.
  have hrr : r<r+1 by rewrite ltrDl ltr01.
  have hh := lt_le_trans (hr (r+1) hrr) (hball (r+1)); by rewrite ltxx in hh.
- have heq : B=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hBempty; by exists x.
  rewrite heq (measure_empty hm) lee_fin; exact hs.
Qed.

(** Source for [federer_2_10_22]: direct theorem of
    2.10.22, pp. 184–186. The asserted
    convergence is the actual extended-real increasing
    order limit, including an infinite limiting mass.
    Targets are arbitrary subsets, with exactly the
    printed finite strictly positive cutoff hypothesis. *)
Theorem federer_2_10_22 (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta : R) (nu : set X -> \bar R) (A : nat -> set X) :
  metric_boundedly_compact X -> 0<delta ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  (forall i j, (i<=j)%N -> A i `<=` A j) ->
  extended_increases_to (fun j=>nu (A j)) (nu (\bigcup_j A j)).
Proof.
move=> hX hd hn hinc.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := metric_scale_envelope_is_measure hn hc0.
have hmass i j (hij : (i<=j)%N) : (nu (A i)<=nu (A j))%E := measure_mono hm (hinc i j hij).
apply: extended_increasing_supremum_limit hmass _; constructor.
- move=> b [j ->]; apply: (@measure_mono R X nu hm)=> x hx; by exists j.
- move=> b hb; case: b hb=> [s| |] hb; [|exact: leey|].
  + have hs : 0<=s.
      have hh := le_trans (measure_nonnegative hm (A 0%N)) (hb _ (ex_intro _ 0%N erefl)).
      by move: hh; rewrite lee_fin.
    apply: (@compact_cost_continuity_common_bound R X c hc delta nu A s hX hd hs hn hinc)=> j.
    apply: hb; by exists j.
  + have hh := le_trans (measure_nonnegative hm (A 0%N)) (hb _ (ex_intro _ 0%N erefl)).
    have hbad := lt_le_trans (ltNyr (0 : R)) hh; by rewrite ltxx in hbad.
Qed.
