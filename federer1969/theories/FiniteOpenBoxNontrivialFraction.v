(** Federer (1969), 3.2.41, printed p. 277: the first
    nontrivial coordinate cut has a strict relative mass lambda.
    Derive that fraction from the actual nonempty smaller box
    families and their finite volumes; no cut mass is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions FiniteDisjointOpenBoxFamilyUP FiniteDisjointOpenBoxVolume
  FiniteOpenBoxLeftCutFamily FiniteOpenBoxRightCutFamily FiniteOpenBoxNontrivialCut
  EuclideanCoordinateHalfspaces MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_nontrivial_fraction]: supporting
    proved first cut and relative masses in Federer 3.2.41, p. 277.
    Both retained index families are nonempty and strictly smaller.
    Actual positive finite side volumes give 0<lambda<1 and the two
    exact original-volume identities. All auxiliary choices are local. *)
Theorem finite_open_box_nontrivial_fraction (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->(1<#|I|)%N ->
  exists (k:'I_n) (t lambda:R),
    (0<#|{: {i:I|(a i k<t)%R}}|<#|I|)%N /\
    (0<#|{: {i:I|(t<b i k)%R}}|<#|I|)%N /\
    0<lambda<1 /\
    @euclidean_lebesgue_measure R n ((\bigcup_i G i) `&` [set x|x k<t])=
      (lambda*fine (@euclidean_lebesgue_measure R n (\bigcup_i G i)))%:E /\
    @euclidean_lebesgue_measure R n ((\bigcup_i G i) `&` [set x|t<x k])=
      ((1-lambda)*fine (@euclidean_lebesgue_measure R n (\bigcup_i G i)))%:E.
Proof.
move=> hG hCard.
have [k [t [hLeftCard hRightCard]]]:=@finite_open_box_nontrivial_coordinate_cut R n I a b G hG hCard.
pose IL:=[the finType of {i:I|a i k<t}].
pose IR:=[the finType of {i:I|t<b i k}].
have [iL _]:=elimT (@card_gt0P IL predT) (andP hLeftCard).1.
have [iR _]:=elimT (@card_gt0P IR predT) (andP hRightCard).1.
have [dL [hL hUL]]:=@finite_open_box_left_cut_family_exists R n I a b G k t hG.
have [cR [hR hUR]]:=@finite_open_box_right_cut_family_exists R n I a b G k t hG.
have /andP[hPL hFL]:=@finite_disjoint_open_box_union_positive_finite R n IL
  (fun i=>a (val i)) dL (fun i=>G (val i) `&` [set x|x k<t]) iL hL.
have /andP[hPR hFR]:=@finite_disjoint_open_box_union_positive_finite R n IR
  cR (fun i=>b (val i)) (fun i=>G (val i) `&` [set x|t<x k]) iR hR.
rewrite hUL in hPL hFL; rewrite hUR in hPR hFR.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose A:set E:=\bigcup_i G i.
pose AL:=A `&` [set x:E|x k<t].
pose AR:=A `&` [set x:E|t<x k].
have hm:=euclidean_lebesgue_is_measure R n.
have hLFinite:mu AL \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm AL)); exact hFL.
have hRFinite:mu AR \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm AR)); exact hFR.
pose l:R:=fine (mu AL).
pose r:R:=fine (mu AR).
have hML:mu AL=l%:E by rewrite /l fineK.
have hMR:mu AR=r%:E by rewrite /r fineK.
have hl:0<l.
  have hPL':(0<mu AL)%E:=hPL; by rewrite hML lte_fin in hPL'.
have hr:0<r.
  have hPR':(0<mu AR)%E:=hPR; by rewrite hMR lte_fin in hPR'.
have hMA:=@euclidean_coordinate_halfspace_volume_split R n k t A.
change (mu A=(mu AL+mu AR)%E) in hMA.
rewrite hML hMR -EFinD in hMA.
pose lambda:R:=l/(l+r).
have hDen:0<l+r:=addr_gt0 hl hr.
have hDen0:l+r!=0 by rewrite gt_eqF.
have hLambda:0<lambda by rewrite /lambda divr_gt0.
have hLambda1:lambda<1.
  rewrite /lambda ltr_pdivrMr // mul1r; lra.
have hLCancel:lambda*(l+r)=l by rewrite /lambda divfK.
have hRCancel:(1-lambda)*(l+r)=r.
  rewrite mulrBl mul1r hLCancel; ring.
exists k,t,lambda; split; first exact hLeftCard.
split; first exact hRightCard.
split; first by apply/andP; split.
split.
- change (mu AL=(lambda*fine (mu A))%:E).
  by rewrite hMA /= hLCancel hML.
- change (mu AR=((1-lambda)*fine (mu A))%:E).
  by rewrite hMA /= hRCancel hMR.
Qed.
