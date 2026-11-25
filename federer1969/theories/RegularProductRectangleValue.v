(** Supporting Federer (1969), 2.10.46, p. 204: Cartesian products of
    regular measures have the expected value on arbitrary rectangles when
    the second factor has finite outer measure. The measurable-rectangle
    identity is 2.6.2(2), p. 115; regular hulls give the upper bound, while
    the covering-section majorant of its proof, p. 116, gives the lower
    bound without measurability. this arbitrary-set consequence is derived
    here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RegularMeasureUP ProductMeasure ProductRectangleValue
  ProductMeasureSequenceInfimum ProductSectionCoverMajorant ProductSections NonnegativeIntegralSetBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_arbitrary_rectangle_lower_finite_second]:
    supporting lower product bound for 2.10.46, p. 204,
    obtained from the section-majorant comparison of 2.6.2,
    p. 116. No measurability or regularity is required
    for this direction. *)
Theorem product_arbitrary_rectangle_lower_finite_second (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  beta B< +oo -> alpha A*beta B<=product_measure ha hb (A `*` B).
Proof.
move=> hfin.
have [hz|hnz] := eqVneq (beta B) 0.
  rewrite hz mule0; exact (measure_nonnegative (product_measure_is_measure ha hb) _).
have hbn := measure_nonnegative hb B.
have hbf : beta B \is a fin_num by rewrite (ge0_fin_numE hbn).
pose b := fine (beta B).
have he : beta B=b%:E := esym (fineK hbf).
have hbp : (0<b)%R.
  have hh : 0<beta B by rewrite lt_def hnz hbn.
  by move: hh; rewrite he lte_fin.
apply: product_measure_sequence_cover_greatest=> C D hCD hcover.
have [f [hf [hi hsec]]] := @product_section_cover_integral_majorant R X Y alpha beta ha hb
  (A `*` B) C D hCD hcover.
have hbound x : A x -> b%:E<=f x.
  move=> hx; have hh := hsec x; by rewrite (product_vertical_rectangle_on B hx) he in hh.
rewrite he muleC; exact (@nonnegative_integral_arbitrary_set_bound R X alpha ha f A b _ hf hbp hbound hi).
Qed.

(** Source for [regular_product_arbitrary_rectangle_finite_second]:
    supporting arbitrary-factor product identity for 2.10.46,
    p. 204. Use equal-measure measurable hulls from
    2.1.5, p. 56, and the independently proved
    lower bound. Finite second mass includes the null endpoint. *)
Theorem regular_product_arbitrary_rectangle_finite_second (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_regular_measure alpha -> is_regular_measure beta -> forall A B,
  beta B< +oo -> product_measure ha hb (A `*` B)=alpha A*beta B.
Proof.
move=> hra hrb A B hfin.
apply/eqP; rewrite eq_le (@product_arbitrary_rectangle_lower_finite_second R X Y alpha beta ha hb A B hfin) andbT.
have [C [hAC [hC hvalA]]] := hra A.
have [D [hBD [hD hvalB]]] := hrb B.
rewrite hvalA hvalB -(product_measure_rectangle_value ha hb hC hD).
apply: (measure_mono (product_measure_is_measure ha hb))=> z [hx hy]; split.
- exact: hAC.
- exact: hBD.
Qed.
