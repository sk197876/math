(** Supporting Federer (1969), 2.10.46, p. 204: lower product bounds from
    uniformly positive section measure. Use the rectangle-cover majorant in
    the proof of 2.6.2, p. 116, followed by the characteristic
    upper-integral comparison of 2.4.5, p. 84. No measurability of the
    covered set, the parameter set, or the section function is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP ProductMeasure ProductSections ProductSectionCoverMajorant
  ProductMeasureSequenceInfimum ProductMeasureTranspose NonnegativeIntegralSetBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_vertical_sections_outer_lower_bound]:
    supporting section comparison for 2.10.46, p. 204,
    from the covering proof of 2.6.2, p. 116.
    A positive constant lower bound on the vertical section
    measures gives that constant times the outer measure of
    the parameter set as a lower bound on product measure. *)
Theorem product_vertical_sections_outer_lower_bound (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X*Y)) (A : set X) (c : R) :
  (0<c)%R -> (forall x, A x -> c%:E<=beta (product_vertical_section S x)) ->
  c%:E*alpha A<=product_measure ha hb S.
Proof.
move=> hc hsec; apply: product_measure_sequence_cover_greatest=> C D hCD hcover.
have [f [hf [hi hbound]]] := @product_section_cover_integral_majorant R X Y alpha beta ha hb
  S C D hCD hcover.
apply: (@nonnegative_integral_arbitrary_set_bound R X alpha ha f A c _ hf hc _ hi)=> x hx.
exact: le_trans (hsec x hx) (hbound x).
Qed.

(** Source for [product_horizontal_sections_outer_lower_bound]:
    horizontal version of the same supporting bound for
    2.10.46, p. 204, using the factor interchange
    in 2.6.5, p. 119. The parameter set and the
    product set are still arbitrary. *)
Theorem product_horizontal_sections_outer_lower_bound (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X*Y)) (A : set Y) (c : R) :
  (0<c)%R -> (forall y, A y -> c%:E<=alpha (product_horizontal_section S y)) ->
  c%:E*beta A<=product_measure ha hb S.
Proof.
move=> hc hs.
have h := @product_vertical_sections_outer_lower_bound R Y X beta alpha hb ha
  (product_transpose S) A c hc hs.
by rewrite product_measure_transpose in h.
Qed.
