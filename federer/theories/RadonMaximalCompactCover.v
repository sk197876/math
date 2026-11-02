(** Federer (1969), 2.5.10, p. 101, final paragraph: G_C covers almost all
    of C. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure
  CountablyClosedFamilyUP MaximalDisjointFamilyUP MaximalDisjointFamilyInsertion
  MeasureRestriction MeasureSupport RadonMeasureUP RadonBorelRegularity RadonFiniteInnerRegularity
  RadonCompactSupport RadonCompactMeetingFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_maximal_compact_almost_cover]: the last assertion of
    Federer 2.5.10, p. 101 Maximality forces the measurable remainder in
    every compact test set to be null. *)
Theorem radon_maximal_compact_almost_cover (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (G : set (set T)) (C : set T) :
  is_maximal_disjoint_family (is_positive_compact_piece mu) G -> compact C ->
  mu (C `\` (\bigcup_(K in compact_meeting_family G C) K))=0.
Proof.
move=> hG hC; pose D := compact_meeting_family G C; pose U := \bigcup_(K in D) K.
have hpiece K : G K -> is_positive_compact_piece mu K.
  exact (@maximal_disjoint_family_members T (@is_positive_compact_piece R T mu) G hG K).
have hcount : countable D := radon_compact_meeting_countable hm hr hpiece
  (maximal_disjoint_family_disjoint hG) hC.
have hUm : measure_measurable mu U.
  apply: (@measure_measurable_countable_union R T [the choiceType of set T] mu hm D (fun K => K) hcount).
  move=> K [hk _]; exact (@radon_compact_measurable R T mu hm hr K (hpiece K hk).1).
have hRm := @measure_measurable_difference R T mu hm C U
  (radon_compact_measurable hm hr hC) hUm.
have hRfin : mu (C `\` U) < +oo.
  apply: le_lt_trans _ (radon_compact_finite hr hC).
  apply: (@measure_mono R T mu hm)=> x [hx _]; exact: hx.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
apply/negP=> hp.
have [Y [hY [hYR hpos]]] := radon_positive_compact_subset hm hr hRm hRfin hp.
pose Z := measure_support (measure_restrict mu Y).
have hZY : Z `<=` Y := compact_restriction_support_within hm hr hY.
have hZC : Z `<=` C by move=> x hx; exact: (hYR x (hZY x hx)).1.
have hZ := compact_restriction_support_piece hm hr hY.
have hne : Z <> set0 := positive_compact_restriction_support_nonempty hm hr hY hpos.
apply: hne; apply: (@maximal_disjoint_family_no_new_piece T
  (is_positive_compact_piece mu) G Z hG hZ)=> K hk.
apply/seteqP; split=> [x [hx hz]|x []].
have hmeet : K `&` C <> set0.
  move=> he; have hh : (K `&` C) x by split=> //; exact: hZC.
  by rewrite he in hh.
have hxu : U x by exists K; first by split.
exact: (hYR x (hZY x hz)).2 hxu.
Qed.
