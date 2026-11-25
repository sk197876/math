(** Federer (1969), 2.6.2, proof p. 116: every subset has an equal-measure
    hull W in P2. This module proves the product-measure equality; the
    equality with the repeated integral is a separate later step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit NonnegativeSum ExtendedRealReciprocalBounds
  ProductMeasure ProductMeasureSequenceInfimum ProductCoverApproximation ProductRectangleHullUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_rectangle_hull]: equal-measure P2 hull
    assertion in Federer 2.6.2, p. 116 Finite product measure uses
    reciprocal-error covers. Infinite product measure uses the entire space,
    as in the printed proof. *)
Theorem product_measure_rectangle_hull (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  exists W, S `<=` W /\ is_countable_rectangle_intersection alpha beta W /\
    measure_measurable (product_measure ha hb) W /\ product_measure ha hb S=product_measure ha hb W.
Proof.
pose nu := product_measure ha hb; have hm := product_measure_is_measure ha hb.
have hpos := @measure_nonnegative R (X * Y)%type nu hm S.
case he: (nu S)=> [r| |]; last by rewrite he in hpos.
- have hex n : exists (A : nat -> set X) (B : nat -> set Y),
      (forall m, measure_measurable alpha (A m) /\ measure_measurable beta (B m)) /\
      S `<=` (\bigcup_m (A m `*` B m)) /\
      nonnegative_sum setT (fun m => alpha (A m) * beta (B m)) < (r + ((n.+1)%:R)^-1)%:E.
    apply: product_measure_sequence_strict_approximation.
    change (nu S < (r + ((n.+1)%:R)^-1)%:E); rewrite he lte_fin ltrDl invr_gt0 ltr0n; by [].
  pose A n := projT1 (cid (hex n)).
  pose B n := projT1 (cid (projT2 (cid (hex n)))).
  have h n := projT2 (cid (projT2 (cid (hex n)))).
  pose W := \bigcap_n (\bigcup_m (A n m `*` B n m)).
  have hSW : S `<=` W by move=> x hx n _; exact: (h n).2.1 x hx.
  have hW : is_countable_rectangle_intersection alpha beta W.
    exists A, B; split=> //; move=> n m; exact: (h n).1 m.
  exists W; split=> //; split=> //; split; first exact: (@countable_rectangle_intersection_measurable R X Y alpha beta ha hb W hW).
  apply/eqP; rewrite eq_le; apply/andP; split.
  + exact: (@measure_mono R (X * Y)%type nu hm S W hSW).
  + change (nu W <= nu S); rewrite he; apply: extended_real_reciprocal_upper_bound=> n.
    have hc : W `<=` \bigcup_m (A n m `*` B n m) by move=> x hx; exact: hx n Logic.I.
    have hbnd := @product_measure_sequence_cover_bound R X Y alpha beta ha hb W (A n) (B n) (h n).1 hc.
    exact: le_trans hbnd (ltW (h n).2.2).
- exists setT; split; first by move=> x hx.
  have hW : is_countable_rectangle_intersection alpha beta (@setT (X * Y)).
    exists (fun _ _ => @setT X), (fun _ _ => @setT Y); split.
    + move=> n m; split; exact: measure_measurable_whole.
    + apply/seteqP; split=> [x _ n _|x hx] //; exists 0%N=> //; by split.
  split=> //; split; first exact: measure_measurable_whole hm.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + exact: (@measure_mono R (X * Y)%type nu hm S setT (fun x hx => Logic.I)).
  + change (nu setT <= nu S); rewrite he; exact: leey.
Qed.
