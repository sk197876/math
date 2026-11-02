(** Federer (1969), 2.10.28(1), p. 191, proof p. 192: every special family H
    satisfies zeta(T)>=sum zeta(T intersect S). Derive the
    endpoint-coordinate estimate from the abstract special-family laws and
    identify its terms with actual set intersections. Endpoint witnesses are
    chosen only locally inside the proof; no interval implementation or
    stronger special-family condition is assumed. Our two-boundary proof
    uses point placeholders instead of its preliminary shrinkage, also
    covering empty intersections. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalGaugeGeometry
  ConcaveIntervalGaugeUP SpecialIntervalFamilyUP IntervalClipLength FiniteIntervalClippingBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_28_1]: direct first
    property of special families in 2.10.28(1),
    p. 191, proof p. 192. Include
    singleton intervals and zero-cost intersections;
    the clipped bound follows from the printed
    whole-member condition and concavity. *)
Theorem federer_2_10_28_1 (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J T : compact_real_intervals R)
    (H : {fset compact_real_intervals R}) :
  is_special_interval_family h J H ->
  \sum_(S <- H) concave_interval_cost h (val T `&` val S)<=concave_interval_cost h (val T).
Proof.
move=> hH.
pose I := compact_real_intervals R.
have hrep (S : I) : exists a b : R, a<=b /\ val S=(`[a,b] : set (real_line_metric R)).
  exact (set_valP S).
pose l (S : I) := projT1 (cid (hrep S)).
pose r (S : I) := projT1 (cid (projT2 (cid (hrep S)))).
have hlaw (S : I) := projT2 (cid (projT2 (cid (hrep S)))).
have hset (S : I) : val S=(`[l S,r S] : set (real_line_metric R)) := (hlaw S).2.
have hord (S : I) : l S<=r S := (hlaw S).1.
have hdis S U (hS : S \in H) (hU : U \in H) (hne : S!=U) : r S<l U \/ r U<l S.
  apply: (@compact_segments_disjoint_endpoints R (l S) (r S) (l U) (r U) (hord S) (hord U)).1.
  rewrite -(hset S) -(hset U); exact (@special_intervals_disjoint R h J H hH S U hS hU hne).
have henv (u v : R) (huv : u<=v) :
    \sum_(S <- H | `[< u<=l S /\ r S<=v >]) h (r S-l S)<=h (v-u).
  have htest : is_compact_real_interval (`[u,v] : set (real_line_metric R)).
    exists u,v; by split.
  pose U : I := Sub (`[u,v] : set (real_line_metric R)) (mem_set htest).
  have hu := @special_interval_envelope R h J H hH U.
  have hcond (S : I) : `[< u<=l S /\ r S<=v >]=`[< val S `<=` val U >].
    apply/idP/idP=> /asboolP hs; apply/asboolP.
    - rewrite (hset S); exact: (@compact_segment_subset_endpoints R (l S) (r S) u v (hord S)).2 hs.
    - have hs' : (`[l S,r S] : set (real_line_metric R)) `<=` `[u,v].
        by rewrite -(hset S).
      exact: (@compact_segment_subset_endpoints R (l S) (r S) u v (hord S)).1 hs'.
  have heq : (\sum_(S <- H | `[< u<=l S /\ r S<=v >]) h (r S-l S))=
      \sum_(S <- H | `[< val S `<=` val U >]) concave_interval_cost h (val S).
    apply: eq_big=> S; first exact: hcond.
    move=> _; by rewrite (hset S) concave_interval_cost_segment.
  rewrite heq; apply: le_trans hu _.
  change (concave_interval_cost h (`[u,v] : set (real_line_metric R))<=h (v-u)).
  by rewrite concave_interval_cost_segment.
have [a [b [hab hT]]] := hrep T.
have hn := @finite_concave_interval_clipping_bound R I h hg H l r a b hab
  (fun S _=>hord S) hdis henv.
have hsumeq : (\sum_(S <- H) concave_interval_cost h ((`[a,b] : set (real_line_metric R)) `&` val S))=
    \sum_(S <- H) h (real_interval_clip_length a b (l S) (r S)).
  apply: eq_big_seq=> S hS.
  by rewrite (hset S) (@concave_interval_intersection_cost R h hg a b (l S) (r S)).
by rewrite hT concave_interval_cost_segment // hsumeq.
Qed.
