(** Federer (1969), 2.6.2(3), proof p. 117: enclose a finite measurable set
    S in W of equal measure, then discard the product-null difference W
    minus S. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  ProductMeasure ProductSections ProductNullSections FiniteRepeatedIntegralHull MeasureNullRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_finite_vertical_fubini]: direct finite- measure case
    of Federer 2.6.2(3), pp. 115, 117 Measurability of S and finiteness of
    its product measure are both retained. *)
Theorem product_finite_vertical_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  measure_measurable (product_measure ha hb) S -> product_measure ha hb S < +oo ->
  measure_almost_everywhere alpha [set x | measure_measurable beta (product_vertical_section S x)] /\
  is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section S x)))
    (product_measure ha hb S).
Proof.
move=> hS hfin.
have [W [hSW [_ [he [hsec hi]]]]] := @product_finite_repeated_integral_hull R X Y alpha beta ha hb S hfin.
pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
have hnum : nu S \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hnu S)).
have hn : nu (W `\` S) = 0.
  have hI : W `&` S = S.
    apply/seteqP; split=> [z [_ hz]|z hz] //; split=> //; exact: hSW z hz.
  have h := hS W; rewrite hI he in h.
  have hc := congr1 (fun t => t - nu S) h.
  by rewrite subee // (addeC (nu S) (nu (W `\` S))) addeK // in hc.
have hnull := @product_null_vertical_sections R X Y alpha beta ha hb (W `\` S) hn.
have hgood : measure_almost_everywhere alpha
    [set x | measure_measurable beta (product_vertical_section S x) /\
      beta (product_vertical_section S x) = beta (product_vertical_section W x)].
  apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hnull)=> x hx.
  apply: (@measurable_subset_null_remainder R Y beta hb _ _ _ (hsec x)).
  - move=> y hy; exact: hSW (x,y) hy.
  - exact hx.
split.
- apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hgood)=> x hx; exact: hx.1.
- rewrite he in hi.
  apply: (@measure_integral_almost_equal R X alpha ha _ _ _ hi).
  apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hgood)=> x [_ hx].
  exists (beta (product_vertical_section S x)); split=> //; exact: esym hx.
Qed.
