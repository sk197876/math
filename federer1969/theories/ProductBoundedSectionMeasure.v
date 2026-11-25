(** Federer (1969), 3.1.4, p. 215: the Fubini estimate of
    bad coordinate increments. A measurable set supported above A,
    with vertical section masses bounded by c, has mass at most c mu(A). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  CountablyMeasurableUP ProductMeasure ProductSections ProductSetFubini
  PartialFunctionBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureExtendedCharacteristicIntegral MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [product_bounded_vertical_sections_measure]:
    supporting Fubini upper bound for S_i in Federer 3.1.4,
    p. 215, from 2.6.2(3), p. 115. Countable measurability
    is explicit; it holds for the bounded measurable sets used there. *)
Theorem product_bounded_vertical_sections_measure (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X*Y)) (A : set X) (c : \bar R) :
  measure_countably_measurable (product_measure ha hb) S ->
  measure_measurable alpha A -> 0<=c ->
  S `<=` A `*` setT ->
  (forall x, A x -> beta (product_vertical_section S x)<=c) ->
  product_measure ha hb S<=c*alpha A.
Proof.
move=> hS hA hc hsupport hbound.
pose s := @CharacteristicFunction.value R X A.
pose hs := @CharacteristicFunction.laws R X A.
have hf := (product_set_fubini hS).2.2.1.
have hg := measure_nonnegative_extended_characteristic_integral ha hs hA hc.
apply: (measure_integral_monotone ha hf hg).
apply: (@measure_almost_everywhere_mono R X alpha ha setT _ _
  (measure_almost_everywhere_true ha))=> x _.
exists (beta (product_vertical_section S x)),(c*(s x)%:E); split=> //; split=> //.
case: (pselect (A x))=> hx.
- rewrite /s (characteristic_on_set hs hx) mule1; exact: hbound.
- rewrite /s (characteristic_off_set hs hx) mule0.
  have he : product_vertical_section S x=set0.
    apply/seteqP; split=> y; last by [].
    by move=> hy; exfalso; apply: hx; exact: (hsupport (x,y) hy).1.
  by rewrite he (measure_empty hb).
Qed.
