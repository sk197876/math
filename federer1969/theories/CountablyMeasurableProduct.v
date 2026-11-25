(** Supporting finite products in Federer (1969), 2.6.5, p. 119. Products of
    countably measurable sets are countably measurable: use all pairs of
    finite measurable covering sets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure ProductRectangleValue
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableSequences
  CountablyMeasurableUnions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_product_rectangle]: Supporting Federer
    2.6.5, p. 119.Empty sets and empty factors are included. *)
Lemma countably_measurable_product_rectangle (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_countably_measurable alpha A -> measure_countably_measurable beta B ->
  measure_countably_measurable (product_measure ha hb) (A `*` B).
Proof.
move=> hA hB.
have [F [hF hFm]] := (proj1 (@countably_measurable_sequence_iff R X alpha ha A)) hA.
have [G [hG hGm]] := (proj1 (@countably_measurable_sequence_iff R Y beta hb B)) hB.
have he : A `*` B = \bigcup_(p in @setT (nat * nat)) (F p.1 `*` G p.2).
  rewrite hF hG; apply/seteqP; split.
  - move=> [x y] [[i _ hxi] [j _ hyj]]; exists (i,j)=> //; by split.
  - by move=> [x y] [[i j] _ [hxi hyj]]; split; [exists i|exists j].
rewrite he; apply: countably_measurable_countable_union; first exact: countableP.
move=> [i j]; apply: finite_measurable_set_countably_measurable.
- exact: (product_measure_measurable_rectangle ha hb (hFm i).1 (hGm j).1).1.
- rewrite (product_measure_rectangle_value ha hb (hFm i).1 (hGm j).1).
  have hfi : alpha (F i) \is a fin_num by rewrite ge0_fin_numE ?(hFm i).2 //; exact (measure_nonnegative ha _).
  have hgj : beta (G j) \is a fin_num by rewrite ge0_fin_numE ?(hGm j).2 //; exact (measure_nonnegative hb _).
  by rewrite -(fineK hfi) -(fineK hgj) -EFinM ltry.
Qed.

(** Source for [product_whole_countably_measurable]: Supporting Federer
    2.6.5, p. 119. *)
Lemma product_whole_countably_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  measure_countably_measurable (product_measure ha hb) setT.
Proof.
move=> hX hY.
have he : @setT (X * Y) = (@setT X) `*` (@setT Y) by apply/seteqP; split=> p _; last by []; split.
rewrite he; exact: countably_measurable_product_rectangle hX hY.
Qed.
