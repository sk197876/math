(** Federer (1969), 3.1.4, p. 215: split the bad coordinate
    increments into exceptional prefix shifts and small scalar sections
    over the remaining prefixes. This supporting estimate is abstract
    in the two factor measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableSubsets
  ProductMeasure ProductSections ProductRectangleValue ProductBoundedSectionMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_exceptional_section_bound]: the first
    inequality for the measure of S_i in Federer 3.1.4, p. 215,
    in two abstract blocks. Prefixes in Z cost their full containing
    section; prefixes outside Z have the prescribed section bound. *)
Theorem product_exceptional_section_bound (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X*Y)) (A Z : set X) (D : set Y) (c : \bar R) :
  measure_countably_measurable (product_measure ha hb) S ->
  measure_measurable alpha A -> measure_measurable alpha Z ->
  measure_measurable beta D -> 0<=c ->
  S `<=` A `*` D ->
  (forall x, A x -> ~Z x -> beta (product_vertical_section S x)<=c) ->
  product_measure ha hb S<=alpha (A `&` Z)*beta D+c*alpha A.
Proof.
move=> hS hA hZ hD hc hs hbound.
pose mu := product_measure ha hb.
pose hm := product_measure_is_measure ha hb.
pose G := S `\` (Z `*` setT).
have hZm : measure_measurable mu (Z `*` setT).
  exact: (product_measure_measurable_rectangle ha hb hZ (measure_measurable_whole hb)).1.
have hGm : measure_measurable mu G.
  exact: (@measure_measurable_difference R [the choiceType of (X*Y)%type] mu hm
    S (Z `*` setT) (countably_measurable_set_measurable hm hS) hZm).
have hG : measure_countably_measurable mu G.
  apply: (@measurable_subset_countably_measurable R [the choiceType of (X*Y)%type]
    mu hm G S hGm _ hS).
  by move=> p [hp _].
have hGbound : mu G<=c*alpha A.
  apply: (product_bounded_vertical_sections_measure hG hA hc).
  - move=> [x y] [hp _]; split=> //; exact: (hs (x,y) hp).1.
  - move=> x hx; case: (pselect (Z x))=> hz.
    + have he : product_vertical_section G x=set0.
        apply/seteqP; split=> y; last by [].
        by move=> [_ hn]; apply: hn; split.
      by rewrite he (measure_empty hb).
    + apply: le_trans _ (hbound x hx hz).
      apply: (measure_mono hb)=> y [hy _]; exact hy.
have hcover : S `<=` ((A `&` Z) `*` D) `|` G.
  move=> [x y] hp; have [hx hy] := hs (x,y) hp.
  case: (pselect (Z x))=> hz.
  - by left; split=> //; split.
  - right; split=> //; by move=> [hz' _]; exact: hz.
apply: le_trans (measure_binary_cover hm hcover) _.
rewrite (product_measure_rectangle_value ha hb
  (measure_measurable_intersection ha hA hZ) hD).
exact: leeD (lexx _) hGbound.
Qed.
