(** Federer (1969), 3.2.23, p. 260, final proof sentence:
    identify the entire product measure from its Borel rectangles.
    This supporting finite-measure argument uses the already proved
    covering maximality of 2.6.1 and Borel regularity, rather than
    introducing another product construction or a uniqueness axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit BorelRegularMeasureUP
  TopologicalBorel ProductMeasure ProductRectangleValue ProductBorelRegularity
  CountableOpenBaseUP BorelProductMeasureBound FiniteBorelMeasureAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_rectangles_determine_product]: supporting
    whole-measure identification in Federer 3.2.23, p. 260.
    Finite Borel-regular factors and countable topological bases
    make rectangle equality sufficient on every subset, including
    nonmeasurable sets. Maximality gives one inequality; finite
    complements and the Borel hull laws give the reverse inequality. *)
Theorem finite_borel_rectangles_determine_product (R:realType) (X Y:topologicalType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (ha:is_measure alpha) (hb:is_measure beta) (rho:set (X*Y)->\bar R)
    (U:nat->set X) (V:nat->set Y):
  is_countable_open_base U ->is_countable_open_base V ->
  is_borel_regular_measure alpha ->is_borel_regular_measure beta ->
  is_measure rho ->is_borel_regular_measure rho ->
  alpha setT< +oo ->beta setT< +oo ->
  (forall A B,borel_set A ->borel_set B ->rho (A `*` B)=alpha A*beta B) ->
  rho=product_measure ha hb.
Proof.
move=>hU hV hAlpha hBeta hr hRho hAFinite hBFinite hRectangle.
pose nu:=product_measure ha hb.
have hn:=product_measure_is_measure ha hb.
have hNu:=product_measure_borel_regular ha hb hU hV hAlpha hBeta.
have hDom:forall S,rho S<=nu S.
  apply:(measure_bounded_by_borel_product_rectangles ha hb hAlpha hBeta hr)=>A B hA hB.
  by rewrite (hRectangle A B hA hB).
have hWhole:(@setT X) `*` (@setT Y)=setT.
  by apply/seteqP; split=>p; [move=>_|move=>_; split].
have hNuTotal:=product_measure_rectangle_value ha hb
  (measure_measurable_whole ha) (measure_measurable_whole hb).
rewrite hWhole in hNuTotal.
have hRhoTotal:=hRectangle setT setT (open_borel_set openT) (open_borel_set openT).
rewrite hWhole in hRhoTotal.
have hTotal:rho setT=nu setT by rewrite /nu hNuTotal.
have hFA:alpha setT \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative ha _)).
have hFB:beta setT \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hb _)).
have hFinite:nu setT< +oo.
  rewrite /nu hNuTotal -(fineK hFA) -(fineK hFB) -EFinM; exact:ltry.
exact:(finite_dominated_borel_regular_measures_agree hr hn hRho hNu hDom hTotal hFinite).
Qed.
