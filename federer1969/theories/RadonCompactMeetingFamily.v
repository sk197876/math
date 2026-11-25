(** Federer (1969), 2.5.10, p. 101, final paragraph: the members of the
    selected disjoint family meeting a compact C form a countable family. We
    obtain a finite-measure open neighborhood directly by Radon outer
    approximation, rather than first finding one with compact closure; this
    gives exactly the bound used in the printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureDisjointSupport
  CountablyClosedFamilyUP RadonMeasureUP RadonBorelRegularity RadonApproximationBounds RadonCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_meeting_family]: the family G_C in Federer 2.5.10,
    p. 101 A member is retained precisely when it meets C. *)
Definition compact_meeting_family (T : topologicalType) (G : set (set T)) (C : set T) :=
  G `&` [set K | K `&` C <> set0].

(** Source for [radon_compact_meeting_countable]: the countability of G_C in
    Federer 2.5.10, p. 101 Inclusion maximality is not needed for this step. *)
Lemma radon_compact_meeting_countable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (G : set (set T)) (C : set T) :
  (forall K, G K -> is_positive_compact_piece mu K) -> set_family_disjoint G ->
  compact C -> countable (compact_meeting_family G C).
Proof.
move=> hG hd hC.
have [V [hV [hCV [hVfin hv]]]] := @radon_finite_open_error R T mu hm hr C 1%R
  (radon_compact_measurable hm hr hC) (radon_compact_finite hr hC) (@ltr01 R).
have hsub K : G K -> K `&` V `<=` V by move=> _ x [_ hx].
have hmeas K : G K -> measure_measurable mu (K `&` V).
  move=> hk; exact: (@measure_measurable_intersection R T mu hm K V
    (radon_compact_measurable hm hr (hG K hk).1) (radon_open_measurable hr hV)).
have hdis K L : G K -> G L -> K <> L -> (K `&` V) `&` (L `&` V)=set0.
  move=> hk hl hne; apply/seteqP; split=> [x [[hx _] [hy _]]|x []].
  have hh : (K `&` L) x by split.
  by rewrite (hd K L hk hl hne) in hh.
have hc := @measure_disjoint_positive_countable R T [the choiceType of set T] mu hm V
  G (fun K => K `&` V) hVfin hsub hmeas hdis.
apply: sub_countable _ hc; apply: subset_card_le=> K [hk hne]; split=> //.
apply: (hG K hk).2 hV _=> he; apply: hne.
apply/seteqP; split=> [x [hx hy]|x []].
have hh : (K `&` V) x by split=> //; exact: hCV.
by rewrite he in hh.
Qed.
