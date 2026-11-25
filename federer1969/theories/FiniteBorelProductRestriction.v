(** Federer (1969), 3.2.23, p. 260: the Cartesian product
    of the two restricted Hausdorff measures. This supporting finite
    Borel-regular identity makes restriction to a pair of compact
    chart images commute with the existing abstract product measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureSplit
  BorelRegularMeasureUP BorelRegularRestriction TopologicalBorel BorelFamilyBasic
  ProductMeasure ProductMeasureUP ProductRectangleValue ProductBorelRectangles ProductBorelRegularity
  CountableOpenBaseUP FiniteBorelProductIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_product_rectangle_restriction]: supporting
    restriction of the Cartesian product to a chart-image rectangle
    in Federer 3.2.23, p. 260. Finite Borel-regular factors
    and Borel factor sets suffice. Equality is of entire measures,
    including their values on nonmeasurable test sets. *)
Theorem finite_borel_product_rectangle_restriction (R:realType) (X Y:topologicalType)
    (alpha:set X->\bar R) (beta:set Y->\bar R) (ha:is_measure alpha) (hb:is_measure beta)
    (U:nat->set X) (V:nat->set Y) (A:set X) (B:set Y):
  is_countable_open_base U ->is_countable_open_base V ->
  is_borel_regular_measure alpha ->is_borel_regular_measure beta ->
  alpha setT< +oo ->beta setT< +oo ->borel_set A ->borel_set B ->
  measure_restrict (product_measure ha hb) (A `*` B)=
    product_measure (measure_restrict_is_measure ha A) (measure_restrict_is_measure hb B).
Proof.
move=>hU hV hAlpha hBeta hAFinite hBFinite hA hB.
pose nu:=product_measure ha hb.
have hn:=product_measure_is_measure ha hb.
have hNu:=product_measure_borel_regular ha hb hU hV hAlpha hBeta.
have hRA:=borel_regular_restrict_borel ha hAlpha hA.
have hRB:=borel_regular_restrict_borel hb hBeta hB.
have hRho:=borel_regular_restrict_borel hn hNu (borel_product_rectangle hA hB).
have hAF:(measure_restrict alpha A) setT< +oo.
  rewrite /measure_restrict setIT.
  exact:(le_lt_trans (measure_mono ha (@subsetT X A)) hAFinite).
have hBF:(measure_restrict beta B) setT< +oo.
  rewrite /measure_restrict setIT.
  exact:(le_lt_trans (measure_mono hb (@subsetT Y B)) hBFinite).
apply:(@finite_borel_rectangles_determine_product R X Y
  (measure_restrict alpha A) (measure_restrict beta B)
  (measure_restrict_is_measure ha A) (measure_restrict_is_measure hb B)
  (measure_restrict nu (A `*` B)) U V hU hV hRA hRB
  (measure_restrict_is_measure hn (A `*` B)) hRho hAF hBF)=>E F hE hF.
have hAE:borel_set (A `&` E):=@borel_family_binary_intersection X setT _ (borel_sets_family X) A E hA hE.
have hBF':borel_set (B `&` F):=@borel_family_binary_intersection Y setT _ (borel_sets_family Y) B F hB hF.
have hRectangle:(A `*` B) `&` (E `*` F)=(A `&` E) `*` (B `&` F).
  by apply/seteqP; split; move=>[x y] [[h1 h2] [h3 h4]]; split; split.
rewrite /measure_restrict hRectangle.
exact:(product_measure_rectangle_value ha hb
  (borel_regular_borel_measurable ha hAlpha hAE)
  (borel_regular_borel_measurable hb hBeta hBF')).
Qed.

(** Source for [product_measure_factors_equal]: supporting
    replacement of equal restricted factors in Federer 3.2.23,
    p. 260. Uniqueness follows from the largest-measure laws
    of 2.6.1, p. 115; no implementation or proof witness
    of the product construction is inspected. *)
Lemma product_measure_factors_equal (R:realType) (X Y:choiceType)
    (alpha alpha':set X->\bar R) (beta beta':set Y->\bar R)
    (ha:is_measure alpha) (ha':is_measure alpha') (hb:is_measure beta) (hb':is_measure beta'):
  alpha=alpha' ->beta=beta' ->product_measure ha hb=product_measure ha' hb'.
Proof.
move=>hA hB; subst alpha'; subst beta'.
exact:(product_measure_unique (product_measure_specification ha hb)
  (product_measure_specification ha' hb')).
Qed.

(** Source for [measure_restrict_nested_subset]: restriction to a
    smaller set absorbs a preceding restriction, by Federer 2.1.2,
    p. 54. This supports the compact-piece product restrictions
    in 3.2.23, p. 260; measurability is unnecessary for this identity. *)
Lemma measure_restrict_nested_subset (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A B:set X):
  B `<=` A ->measure_restrict (measure_restrict mu A) B=measure_restrict mu B.
Proof.
move=>hSub; apply:funext=>S; rewrite /measure_restrict.
congr (mu _); apply/seteqP; split.
- by move=>x [_ hx].
- move=>x [hx hS]; split; first exact:hSub x hx.
  by split.
Qed.
