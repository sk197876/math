(** Federer (1969), 2.9.20, p. 166: localise the equality between variation
    and the absolute derivative integral by splitting an interval at two
    points. The supporting measure identity follows from 2.1.3(7), p. 55.
    Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [atomless_segment_measure_split]: supporting finite interval
    additivity for Federer 2.9.20, p. 166 Inclusion-exclusion leaves just
    the common endpoint, whose mass is zero. Degenerate segments and
    possibly infinite nonnegative interval masses are included. *)
Lemma atomless_segment_measure_split (R : realType) (mu : set R -> \bar R)
    (a b c : R) : (a<=b)%R -> (b<=c)%R ->
  measure_measurable mu `[a,b] -> mu [set b]=0 ->
  mu `[a,c]=mu `[a,b]+mu `[b,c].
Proof.
move=> hab hbc hA hb.
have hI : (`[a,b] : set R) `&` `[b,c]=[set b].
  apply/seteqP; split.
  - move=> x [hx hy]; move: hx hy; rewrite /= !in_itv /= => /andP[_ hxb] /andP[hbx _].
    by apply/eqP; rewrite eq_le hxb hbx.
  - move=> x ->; split; by rewrite /= in_itv /= lexx ?hab ?hbc.
have hU : (`[a,b] : set R) `|` `[b,c]=`[a,c].
  apply/seteqP; split.
  - move=> x [hx|hx]; move: hx; rewrite /= !in_itv /=.
    + by move=> /andP[hax hxb]; rewrite hax (le_trans hxb hbc).
    + by move=> /andP[hbx hxc]; rewrite (le_trans hab hbx) hxc.
  - move=> x; rewrite /= in_itv /= => /andP[hax hxc].
    case: (leP x b)=> hxb.
    + left; by rewrite /= in_itv /= hax hxb.
    + right; by rewrite /= in_itv /= (ltW hxb) hxc.
have h := @measure_inclusion_exclusion R R mu `[a,b] `[b,c] hA.
by rewrite hI hU hb add0e in h.
Qed.
