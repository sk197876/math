(** Supporting finite disjoint interval unions in Federer (1969), 2.9.20, p.
    166 A null included left endpoint may be removed from a half-open cell.
    No condition on its excluded right endpoint is needed. Source context
    and the dyadic proof route: DyadicIntervalFamilies.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_half_open_remove_left_atom]: supporting endpoint
    removal in the open-set step of Federer 2.9.20, p. 166 The difference
    [u,v) minus (u,v) is contained in {u}; a null left atom thus makes their
    masses equal. The right endpoint is excluded in both sets, so it need
    not be a continuity point of a curve. *)
Lemma measure_half_open_remove_left_atom (R : realType) (mu : set R -> \bar R)
    (u v : R) : is_measure mu -> mu [set u]=0 -> mu `[u,v[=mu `]u,v[.
Proof.
move=> hm hu; apply/eqP; rewrite eq_le; apply/andP; split.
- apply (@null_remainder_measure_cover_bound R R mu `[u,v[ `]u,v[ hm).
  apply: (@measure_null_subset R R mu hm _ [set u]) hu.
  move=> x [hx hn]; move: hx; rewrite /= in_itv /= => /andP[hux hxv].
  have hxu : x=u.
    apply/eqP; rewrite eq_le hux andbT leNgt; apply/negP=> hux'.
    apply: hn; by rewrite /= in_itv /= hux' hxv.
  exact hxu.
- apply (@measure_mono R R mu hm `]u,v[ `[u,v[)=> x.
  rewrite /= !in_itv /= => /andP[hux hxv].
  by rewrite (ltW hux) hxv.
Qed.
