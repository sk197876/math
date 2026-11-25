(** Federer (1969), 2.6.2(2), pp. 115–117: the second-coordinate cylinder
    case of rectangle measurability. We apply the printed rectangle
    splitting directly to covering costs, as explained in
    ProductFirstCylinder.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure NonnegativeSum NonnegativeSumAdd
  ProductMeasure ProductMeasureSequenceInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_second_cylinder_measurable]: supporting case of
    Federer 2.6.2(2), pp. 115–117 The argument retains the full generality
    of the factor measures. *)
Lemma product_second_cylinder_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (B : set Y) :
  measure_measurable beta B -> measure_measurable (product_measure ha hb) (setT `*` B).
Proof.
move=> hB T; apply/eqP; rewrite eq_le (measure_split_upper (product_measure_is_measure ha hb)) /=.
apply: (product_measure_sequence_cover_greatest ha hb)=> C D hCD hc.
have hm1 n : measure_measurable alpha (C n) /\ measure_measurable beta (D n `&` B).
  split; first exact: (hCD n).1.
  exact: (@measure_measurable_intersection R Y beta hb _ _ (hCD n).2 hB).
have hm2 n : measure_measurable alpha (C n) /\ measure_measurable beta (D n `\` B).
  split; first exact: (hCD n).1.
  exact: (@measure_measurable_difference R Y beta hb _ _ (hCD n).2 hB).
have hc1 : T `&` (setT `*` B) `<=` \bigcup_n (C n `*` (D n `&` B)).
  move=> [x y] [ht [_ hy]]; have [n _ [hxn hyn]] := hc (x,y) ht.
  exists n=> //; split=> //; by split.
have hc2 : T `\` (setT `*` B) `<=` \bigcup_n (C n `*` (D n `\` B)).
  move=> [x y] [ht hn]; have [n _ [hxn hyn]] := hc (x,y) ht.
  exists n=> //; split=> //; split=> //; move=> hy; apply: hn; by split.
have h1 := @product_measure_sequence_cover_bound R X Y alpha beta ha hb _ _ _ hm1 hc1.
have h2 := @product_measure_sequence_cover_bound R X Y alpha beta ha hb _ _ _ hm2 hc2.
have hn1 n : setT n -> 0 <= alpha (C n) * beta (D n `&` B).
  move=> _; exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
have hn2 n : setT n -> 0 <= alpha (C n) * beta (D n `\` B).
  move=> _; exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
have hs := leeD h1 h2.
rewrite -(@nonnegative_sum_add R [the choiceType of (nat : Type)] setT _ _ hn1 hn2) in hs.
apply: le_trans hs _; apply: nonnegative_sum_mono=> n _.
rewrite -(ge0_muleDr (alpha (C n)) (measure_nonnegative hb _) (measure_nonnegative hb _)).
by rewrite -(hB (D n)).
Qed.
