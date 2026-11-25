(** Federer (1969), 3.3.20, p. 307, published erratum p. 6:
    exact lengths of the original finite unions of projected intervals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground LebesgueScalarMeasure EuclideanLebesgueBoxes
  MeasureUP MeasureFiniteAdditivity MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_lebesgue_point_overlap_union]:
    supporting addition of original projected interval
    lengths in 3.3.20, p. 307,
    corrected by published erratum p. 6,
    book p. 307 line 26. A
    possible common endpoint has zero mass; the
    second original set need not be measurable. *)
Lemma scalar_lebesgue_point_overlap_union (R:realType) (A B:set R) (c:R):
  measure_measurable (@lebesgue_scalar_measure R) A ->A `&` B `<=` [set c] ->
  lebesgue_scalar_measure (A `|` B)=
    (lebesgue_scalar_measure A+lebesgue_scalar_measure B)%E.
Proof.
move=>hA hOverlap.
have hZero:=@measure_null_subset R [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (A `&` B) [set c] hOverlap (lebesgue_scalar_singleton c).
have h:=@measure_inclusion_exclusion R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) A B hA.
by rewrite hZero add0e in h.
Qed.

(** Source for [scalar_lebesgue_two_ordered_segments]:
    supporting exact two-interval branch of the
    corrected projection calculation in 3.3.20,
    p. 307; published erratum p. 6,
    book p. 307 line 26. Touching
    closed endpoints and degenerate segments remain. *)
Lemma scalar_lebesgue_two_ordered_segments (R:realType) (a b c d:R):
  a<=b ->b<=c ->c<=d ->
  lebesgue_scalar_measure ((`[a,b] `|` `[c,d]):set R)=(b-a+(d-c))%:E.
Proof.
move=>hab hbc hcd.
have hOverlap:((`[a,b] `&` `[c,d]):set R) `<=` [set b].
  move=>x [hx hy];move:hx hy;rewrite /= !in_itv /= =>/andP[_ hxb] /andP[hcx _].
  by apply/eqP;rewrite eq_le hxb (le_trans hbc hcx).
rewrite (@scalar_lebesgue_point_overlap_union R `[a,b] `[c,d] b
  (lebesgue_scalar_segment_measurable a b) hOverlap)
  (lebesgue_scalar_segment hab) (lebesgue_scalar_segment hcd) -EFinD.
by [].
Qed.

(** Source for [scalar_lebesgue_three_ordered_segments]:
    supporting exact three-interval branch of the
    corrected projection calculation in 3.3.20,
    p. 307; published erratum p. 6,
    book p. 307 line 26. All
    original closed endpoints are retained. *)
Lemma scalar_lebesgue_three_ordered_segments (R:realType) (a b c d e f:R):
  a<=b ->b<=c ->c<=d ->d<=e ->e<=f ->
  lebesgue_scalar_measure ((`[a,b] `|` `[c,d] `|` `[e,f]):set R)=
    (b-a+(d-c)+(f-e))%:E.
Proof.
move=>hab hbc hcd hde hef.
have hOverlap:((`[e,f] `&` (`[a,b] `|` `[c,d])):set R) `<=` [set e].
  move=>x [hx [hy|hy]];move:hx hy;rewrite /= !in_itv /= =>/andP[hex _] /andP[_ hUpper];
    apply/eqP;rewrite eq_le;apply/andP;split;nra.
rewrite setUC (@scalar_lebesgue_point_overlap_union R `[e,f] (`[a,b] `|` `[c,d]) e
  (lebesgue_scalar_segment_measurable e f) hOverlap)
  (lebesgue_scalar_segment hef) (scalar_lebesgue_two_ordered_segments hab hbc hcd) -EFinD.
congr (_%:E);ring.
Qed.
