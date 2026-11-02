(** Federer (1969), 2.6.2(2), pp. 115–117: measurable rectangles. This
    supporting first-coordinate cylinder case uses the same rectangle
    splitting on pp. 116–117, directly on the defining covering sums. This
    avoids introducing the repeated- integral class solely for
    measurability; the integral identities are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure NonnegativeSum NonnegativeSumAdd
  ProductMeasure ProductMeasureSequenceInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_first_cylinder_measurable]: supporting case of
    Federer 2.6.2(2), pp. 115–117 Splitting the first coordinate of every
    covering rectangle gives the Caratheodory equality, including infinite
    factor measures and arbitrary test sets. *)
Lemma product_first_cylinder_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) :
  measure_measurable alpha A -> measure_measurable (product_measure ha hb) (A `*` setT).
Proof.
move=> hA T; apply/eqP; rewrite eq_le (measure_split_upper (product_measure_is_measure ha hb)) /=.
apply: (product_measure_sequence_cover_greatest ha hb)=> C D hCD hc.
have hm1 n : measure_measurable alpha (C n `&` A) /\ measure_measurable beta (D n).
  split; last exact: (hCD n).2.
  exact: (@measure_measurable_intersection R X alpha ha _ _ (hCD n).1 hA).
have hm2 n : measure_measurable alpha (C n `\` A) /\ measure_measurable beta (D n).
  split; last exact: (hCD n).2.
  exact: (@measure_measurable_difference R X alpha ha _ _ (hCD n).1 hA).
have hc1 : T `&` (A `*` setT) `<=` \bigcup_n ((C n `&` A) `*` D n).
  move=> [x y] [ht [hx _]]; have [n _ [hxn hyn]] := hc (x,y) ht.
  exists n=> //; split=> //; by split.
have hc2 : T `\` (A `*` setT) `<=` \bigcup_n ((C n `\` A) `*` D n).
  move=> [x y] [ht hn]; have [n _ [hxn hyn]] := hc (x,y) ht.
  exists n=> //; split=> //; split=> //; move=> hx; apply: hn; by split.
have h1 := @product_measure_sequence_cover_bound R X Y alpha beta ha hb _ _ _ hm1 hc1.
have h2 := @product_measure_sequence_cover_bound R X Y alpha beta ha hb _ _ _ hm2 hc2.
have hn1 n : setT n -> 0 <= alpha (C n `&` A) * beta (D n).
  move=> _; exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
have hn2 n : setT n -> 0 <= alpha (C n `\` A) * beta (D n).
  move=> _; exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
have hs := leeD h1 h2.
rewrite -(@nonnegative_sum_add R [the choiceType of (nat : Type)] setT _ _ hn1 hn2) in hs.
apply: le_trans hs _; apply: nonnegative_sum_mono=> n _.
rewrite -(ge0_muleDl (beta (D n)) (measure_nonnegative ha _) (measure_nonnegative ha _)).
by rewrite -(hA (C n)).
Qed.
