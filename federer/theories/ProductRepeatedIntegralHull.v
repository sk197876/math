(** Federer (1969), 2.6.2, p. 116: every subset has an enclosing P2 set with
    the same product measure and repeated integral, including the
    infinite-measure case. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic
  MeasureSplit MeasureIntegralUP ProductMeasure ProductRectangleHullUP ProductSections
  CountableRectangleUnionUP CountableRectangleIntersections CountableRectangleFubini FiniteRepeatedIntegralHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_repeated_integral_hull]: complete
    displayed enclosing-set assertion of Federer 2.6.2,
    p. 116. For infinite product measure, take W=X times Y,
    as in the next paragraph; finite measure uses the decreasing
    rectangle-union construction. No measurability of S is required. *)
Theorem product_repeated_integral_hull (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  exists W, S `<=` W /\ is_countable_rectangle_intersection alpha beta W /\
    product_measure ha hb W = product_measure ha hb S /\
    (forall x, measure_measurable beta (product_vertical_section W x)) /\
    is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section W x)))
      (product_measure ha hb W).
Proof.
case hfin : (product_measure ha hb S < +oo).
- exact (@product_finite_repeated_integral_hull R X Y alpha beta ha hb S hfin).
- have he : product_measure ha hb S = +oo by apply/eqP; rewrite -leye_eq leNgt hfin.
  have hw : product_measure ha hb setT = product_measure ha hb S.
    apply/eqP; rewrite eq_le; apply/andP; split; first by rewrite he; exact: leey.
    apply: (measure_mono (product_measure_is_measure ha hb))=> z hz; by [].
  have hp := @countable_rectangle_union_whole R X Y alpha beta ha hb.
  have hP2 : is_countable_rectangle_intersection alpha beta (@setT (X * Y)).
    have [A [B [hm hc]]] := hp; exists (fun _ => A), (fun _ => B); split=> //.
    apply/seteqP; split=> z hz.
    + move=> n _; rewrite -hc; by [].
    + by [].
  exists setT; split; first by move=> z hz.
  split=> //; split=> //; split.
  + exact (@countable_rectangle_union_sections_measurable R X Y alpha beta hb setT hp).
  + exact (@countable_rectangle_union_vertical_integral R X Y alpha beta ha hb setT hp).
Qed.
