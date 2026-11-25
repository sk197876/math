(** Federer (1969), 2.10.28(1), pp. 191–192: real interval geometry for
    clipping the special family by a test interval. These are supporting
    endpoint identities, not separately asserted claims of the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_segment_intersection]: supporting
    exact intersection used in 2.10.28(1),
    p. 192. When the maximum left endpoint
    exceeds the minimum right endpoint, both
    sides denote the empty set. *)
Lemma compact_segment_intersection (R : realType) (a b c d : R) :
  (`[a,b] : set (real_line_metric R)) `&` `[c,d]=`[Order.max a c,Order.min b d].
Proof.
apply/seteqP; split=> x.
- move=> [h1 h2]; move: h1 h2; rewrite /= !in_itv /= => /andP[hax hxb] /andP[hcx hxd].
  by rewrite ge_max le_min hax hcx hxb hxd.
- rewrite /= in_itv /= ge_max le_min=> /andP [/andP[hax hcx] /andP[hxb hxd]].
  split; by rewrite /= in_itv /= ?hax ?hcx ?hxb ?hxd.
Qed.

(** Source for [compact_segment_subset_endpoints]: supporting
    test-interval containment in the definition of
    special in 2.10.28, p. 191. A
    nonempty closed interval is contained precisely
    when its two endpoints are contained. *)
Lemma compact_segment_subset_endpoints (R : realType) (a b c d : R) : a<=b ->
  ((`[a,b] : set (real_line_metric R)) `<=` `[c,d] <-> c<=a /\ b<=d).
Proof.
move=> hab; split.
- move=> hs.
  have ha : (`[a,b] : set (real_line_metric R)) a by rewrite /= in_itv /= lexx hab.
  have hb : (`[a,b] : set (real_line_metric R)) b by rewrite /= in_itv /= lexx hab.
  have /andP[hca _] : c<=a<=d by move: (hs a ha); rewrite /= in_itv.
  have /andP[_ hbd] : c<=b<=d by move: (hs b hb); rewrite /= in_itv.
  by split.
- move=> [hca hbd] x; rewrite /= !in_itv /= => /andP[hax hxb].
  by rewrite (le_trans hca hax) (le_trans hxb hbd).
Qed.

(** Source for [compact_segments_disjoint_endpoints]: supporting
    strict separation of distinct closed members
    of a special family in 2.10.28(1),
    p. 192. A shared endpoint prevents
    disjointness, including singleton intervals. *)
Lemma compact_segments_disjoint_endpoints (R : realType) (a b c d : R) : a<=b -> c<=d ->
  ((`[a,b] : set (real_line_metric R)) `&` `[c,d]=set0 <-> b<c \/ d<a).
Proof.
move=> hab hcd; split.
- move=> he; case: (ltP b c)=> hbc; first by left.
  case: (ltP d a)=> hda; first by right.
  have hx : ((`[a,b] : set (real_line_metric R)) `&` `[c,d]) (Order.max a c).
    split; rewrite /= in_itv /=.
    + rewrite le_max lexx ge_max hab hbc; by [].
    + rewrite le_max lexx orbT ge_max hda hcd; by [].
  by rewrite he in hx.
- move=> [hbc|hda]; apply/seteqP; split=> [x [hx hy]|x []];
    move: hx hy; rewrite /= !in_itv /= => /andP[hax hxb] /andP[hcx hxd]; lra.
Qed.

(** Source for [concave_interval_intersection_cost]: supporting
    zeta(T intersect S) in 2.10.28(1),
    p. 191, as h of the nonnegative
    clipped length. Empty intersections and
    point intersections have cost h(0)=0. *)
Lemma concave_interval_intersection_cost (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (a b c d : R) :
  concave_interval_cost h ((`[a,b] : set (real_line_metric R)) `&` `[c,d])=
    h (Order.max 0 (Order.min b d-Order.max a c)).
Proof.
rewrite compact_segment_intersection.
case: (leP (Order.max a c) (Order.min b d))=> hle.
- have hlen : 0<=Order.min b d-Order.max a c by rewrite subr_ge0.
  by rewrite (@concave_interval_cost_segment R h _ _ hle) (max_r hlen).
- have he : (`[Order.max a c,Order.min b d] : set (real_line_metric R))=set0.
    apply/seteqP; split=> [x hx|x []].
    have /andP[hl hr] : Order.max a c<=x<=Order.min b d by move: hx; rewrite /= in_itv.
    by have hh := lt_le_trans hle (le_trans hl hr); rewrite ltxx in hh.
  rewrite he (concave_interval_cost_empty hg) max_l; last by lra.
  by rewrite (interval_gauge_zero hg).
Qed.
