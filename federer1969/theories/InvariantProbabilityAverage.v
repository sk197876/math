(** Federer (1969), 3.2.48, p. 286: averaging a finite source
    measure over continuous measure-preserving transformations leaves it
    unchanged. Supporting all-set image-measure form of the Fubini step,
    using true Borel hulls and the outer section bound of 2.6.2. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureRestriction MeasurePushforward
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages CountableOpenBaseUP
  ProductMeasure ProductBorelRegularity ProductSections ProductBoundedSectionMeasure
  ProductSectionOuterBound CountablyMeasurableBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [invariant_probability_average_pushforward]: the actual
    source measure is unchanged by the probability average in 3.2.48,
    p. 286. Equality holds on arbitrary subsets. The upper bound uses
    a true Borel hull; the lower bound uses outer section measures, and
    never declares a nonmeasurable source's hull difference null. *)
Theorem invariant_probability_average_pushforward (R:realType) (G X:topologicalType)
    (alpha:set G->\bar R) (beta:set X->\bar R)
    (ha:is_measure alpha) (hb:is_measure beta)
    (U:nat->set G) (V:nat->set X) (F:G*X->X):
  is_countable_open_base U ->is_countable_open_base V ->
  is_borel_regular_measure alpha ->is_borel_regular_measure beta ->
  alpha setT= 1 ->beta setT< +oo ->continuous F ->
  (forall g,measure_pushforward (fun x=>F (g,x)) beta=beta) ->
  measure_pushforward F (product_measure ha hb)=beta.
Proof.
move=>hU hV hRA hRB hTotal hFinite hF hInvariant.
pose rho:=product_measure ha hb.
have hr:=product_measure_is_measure ha hb.
have hReg:=product_measure_borel_regular ha hb hU hV hRA hRB.
have hWhole:(setT:set (G*X))=(setT:set G) `*` (setT:set X).
  by apply/seteqP; split=>z _; [split|exact I].
have hRhoFinite:rho setT< +oo.
  have hBound:=product_measure_rectangle_bound ha hb (@measure_measurable_whole R G alpha ha)
    (@measure_measurable_whole R X beta hb).
  rewrite -hWhole hTotal mul1e in hBound.
  exact (le_lt_trans hBound hFinite).
have hSection T g:beta (product_vertical_section (F @^-1` T) g)=beta T.
  have h:=congr1 (fun nu:set X->\bar R=>nu T) (hInvariant g).
  exact h.
apply:funext=>T; apply/eqP; rewrite eq_le; apply/andP; split.
- have [C [hTC [hCB hMass]]]:=borel_regular_cover hRB T.
  have hPreB:borel_set (F @^-1` C):=continuous_borel_preimage hF hCB.
  have hPreM:=borel_regular_borel_measurable hr hReg hPreB.
  have hPreFinite:rho (F @^-1` C)< +oo.
    exact (le_lt_trans (measure_mono hr (fun x _=>I)) hRhoFinite).
  have hCount:=finite_measurable_set_countably_measurable hPreM hPreFinite.
  have hSectionBound g:beta (product_vertical_section (F @^-1` C) g)<=beta C by rewrite hSection.
  have hBound:=@product_bounded_vertical_sections_measure R G X alpha beta ha hb
    (F @^-1` C) setT (beta C) hCount (@measure_measurable_whole R G alpha ha)
    (measure_nonnegative hb C) (fun x _=>conj I I) (fun g _=>hSectionBound g).
  rewrite hTotal mule1 in hBound.
  have hMono:rho (F @^-1` T)<=rho (F @^-1` C).
    exact (@measure_mono R (G*X)%type rho hr (F @^-1` T) (F @^-1` C)
      (fun x hx=>hTC (F x) hx)).
  change (rho (F @^-1` T)<=beta T); rewrite hMass.
  exact (le_trans hMono hBound).
- change (beta T<=rho (F @^-1` T)).
  have hTF:beta T< +oo:=le_lt_trans (measure_mono hb (fun x _=>I)) hFinite.
  have hTN:=measure_nonnegative hb T.
  case hMass:(beta T)=>[r| |].
  + have hr0:(0<=r)%R by move:hTN; rewrite hMass lee_fin.
    have [hZero|hNonzero]:=eqVneq r 0%R.
    * rewrite hZero; exact (measure_nonnegative hr _).
    * have hrPos:(0<r)%R by rewrite lt_def hNonzero hr0.
      have hLowerSection g:r%:E<=beta (product_vertical_section (F @^-1` T) g).
        by rewrite hSection hMass.
      have hBound:=@product_vertical_sections_outer_lower_bound R G X alpha beta ha hb
        (F @^-1` T) setT r hrPos (fun g _=>hLowerSection g).
      by rewrite hTotal mule1 in hBound.
  + by move:hTF; rewrite hMass ltxx.
  + by move:hTN; rewrite hMass.
Qed.
