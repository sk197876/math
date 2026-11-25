(** Federer (1969), 2.6.2, p. 116: P1 is stable under finite intersections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure CountableRectangleUnionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_rectangle_union_whole]: supporting
    whole-space member of P0, hence P1, used for the
    infinite-measure hull case in Federer 2.6.2, p. 116. *)
Lemma countable_rectangle_union_whole (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_countable_rectangle_union alpha beta (@setT (X * Y)).
Proof.
exists (fun _ => @setT X), (fun _ => @setT Y); split.
- move=> n; split; exact: measure_measurable_whole.
- apply/seteqP; split=> [z _|z hz] //; exists 0%N=> //; by split.
Qed.

(** Source for [countable_rectangle_union_intersection]: direct stability of
    P1 under intersection of two members in Federer 2.6.2, p. 116 *)
Lemma countable_rectangle_union_intersection (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S T : set (X * Y)) :
  is_countable_rectangle_union alpha beta S -> is_countable_rectangle_union alpha beta T ->
  is_countable_rectangle_union alpha beta (S `&` T).
Proof.
move=> [A [B [hm ->]]] [C [D [hn ->]]].
pose F (ij : nat * nat) := (A ij.1 `&` C ij.2, B ij.1 `&` D ij.2).
pose G := F @` setT.
have hc : countable G := sub_countable (card_image_le F setT) (countableP setT).
have hG p : G p -> measure_measurable alpha p.1 /\ measure_measurable beta p.2.
  move=> [[i j] _ <-]; split.
  - exact (@measure_measurable_intersection R X alpha ha (A i) (C j) (hm i).1 (hn j).1).
  - exact (@measure_measurable_intersection R Y beta hb (B i) (D j) (hm i).2 (hn j).2).
have he : (\bigcup_i (A i `*` B i)) `&` (\bigcup_j (C j `*` D j)) =
    \bigcup_(p in G) (p.1 `*` p.2).
  apply/seteqP; split.
  - move=> [x y] [[i _ [ha' hb']] [j _ [hc' hd']]].
    exists (F (i,j)); first by exists (i,j).
    by split; split.
  - move=> [x y] [p [[i j] _ <-] [[ha' hc'] [hb' hd']]].
    split; [exists i|exists j]=> //; by split.
rewrite he; exact (@countable_rectangle_family_union R X Y alpha beta ha hb G hc hG).
Qed.
