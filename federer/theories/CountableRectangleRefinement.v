(** Federer (1969), 2.6.2, p. 116: every countable union of measurable
    rectangles is a countable disjoint union of measurable rectangles. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP SetSequenceDisjointification
  DisjointRectangleCoverUP FiniteRectangleDifferences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_rectangle_prefix_difference]: supporting finite
    subtraction induction in Federer 2.6.2, p. 116 Subtracting a finite
    initial union preserves the finite disjoint-rectangle form. *)
Lemma finite_rectangle_prefix_difference (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X * Y)) (A : nat -> set X) (B : nat -> set Y) :
  finite_disjoint_rectangle_union alpha beta S ->
  (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) ->
  forall n, finite_disjoint_rectangle_union alpha beta
    (S `\` set_sequence_prefix (fun k => A k `*` B k) n).
Proof.
move=> hs hm; elim=> [|n IH].
- by rewrite set_sequence_prefix_zero setD0.
- have he : S `\` set_sequence_prefix (fun k => A k `*` B k) n.+1 =
      (S `\` set_sequence_prefix (fun k => A k `*` B k) n) `\` (A n `*` B n).
    by rewrite set_sequence_prefix_succ !setDE setCU setIA.
  rewrite he; exact (@finite_rectangle_union_difference R X Y alpha beta ha hb _ _ _ IH (hm n).1 (hm n).2).
Qed.

(** Source for [countable_disjoint_rectangle_refinement]: direct P1
    decomposition assertion in Federer 2.6.2, p. 116 The output family is
    specified by measurable factors, disjointness, and the unchanged union.
    Repeated and empty input rectangles are permitted. *)
Theorem countable_disjoint_rectangle_refinement (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (A : nat -> set X) (B : nat -> set Y) :
  (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) ->
  exists G, countable G /\ is_disjoint_rectangle_cover alpha beta G (\bigcup_n (A n `*` B n)).
Proof.
move=> hm; pose F n := A n `*` B n.
have hex n : finite_disjoint_rectangle_union alpha beta (set_sequence_disjointify F n).
  apply: (@finite_rectangle_prefix_difference R X Y alpha beta ha hb (F n) A B _ hm n).
  exact (@rectangle_finite_disjoint_union R X Y alpha beta (A n) (B n) (hm n).1 (hm n).2).
pose G n := projT1 (cid (hex n)).
have hg n := projT2 (cid (hex n)).
pose H := \bigcup_n G n.
exists H; split.
- apply: bigcup_countable (countableP setT) _=> n _; exact: finite_set_countable (hg n).1.
- constructor.
  + move=> p [n _ hp]; exact (@disjoint_rectangle_factors R X Y alpha beta (G n) _ (hg n).2 p hp).
  + move=> p q [n _ hp] [m _ hq] hne z hzp hzq.
    have [enm|hnm] := eqVneq n m.
    * subst m; exact (@disjoint_rectangle_pieces R X Y alpha beta (G n) _ (hg n).2 p q hp hq hne z hzp hzq).
    * have hn := @disjoint_rectangle_cover_subset R X Y alpha beta (G n) _ (hg n).2 p hp z hzp.
      have hm' := @disjoint_rectangle_cover_subset R X Y alpha beta (G m) _ (hg m).2 q hq z hzq.
      exact: (@set_sequence_disjointify_disjoint (X * Y)%type F n m hnm z hn hm').
  + change ((\bigcup_n F n) = \bigcup_(p in H) (p.1 `*` p.2)).
    rewrite -set_sequence_disjointify_union; apply/seteqP; split.
    * move=> z [n _ hn]; rewrite (disjoint_rectangle_union (hg n).2) in hn.
      have [p hp hzp] := hn; exists p=> //; by exists n.
    * move=> z [p [n _ hp] hzp]; exists n=> //.
      exact: (@disjoint_rectangle_cover_subset R X Y alpha beta (G n) _ (hg n).2 p hp z hzp).
Qed.
