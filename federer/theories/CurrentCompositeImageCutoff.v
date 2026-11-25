(** Federer (1969), 4.1.7, p. 359:
    composition requires an intermediate test
    replacement near the full f(spt T),
    which can be larger than spt(f#T).
    The original composite-properness hypothesis makes
    its inverse target-support locus compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentProperSupport CurrentProperSupportDomain CurrentCompositeProperness SmoothFormPullbackComposition
  SmoothFormPullbackSealed SmoothPullbackCutoffTests SmoothCompactSet SmoothFunctionSupport
  IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompositeImageCutoff.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n q m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R q).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R q)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R q)).
Variables (U:set X) (V:set Y) (W:set Z).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Hypothesis hW:forall z,W z->norm_domain_interior NZ W z.
Arguments hW : clear implicits.
Variables (f:X->Y) (g:Y->Z).
Hypothesis hFImage:forall x,U x->V (f x).
Arguments hFImage : clear implicits.
Hypothesis hGImage:forall y,V y->W (g y).
Arguments hGImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNY hNZ V g.
Variable T:@current_space R h2 v U hU m.
Local Notation support := (@current_support R h2 v U hU m T).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Local Notation ZT := (real_norm_metric_space hNZ).
Local Notation VT := (current_domain R n V).
Local Notation WT := (current_domain R q W).
Local Notation ST := [the topologicalType of set_type (support:set XT)].
Local Notation fS := (@current_map_on_support R h2 v n m U hU V T f hFImage).
Local Notation gV := (@current_map_on_domain R n q V W g hGImage).
Local Notation hGFImage := (@current_smooth_composite_image R v n q U V W f g hFImage hGImage).
Hypothesis hpGF:@is_current_proper_on_support R h2 v q m U hU W T (fun x=>g (f x)) hGFImage.
Local Notation properData := (@current_composite_support_properness R h2 v n q m U V W hU
  f g hFImage hGImage hf hg T hpGF).
Local Notation E := (@current_smooth_space R h2 q W hW m).
Local Notation ev := (@current_smooth_value R h2 q W hW m).
Local Notation F := (@current_test_space R h2 n V hV m).
Local Notation fv := (@current_test_value R h2 n V hV m).
Local Notation gv := (@current_smooth_value R h2 n V hV m).
Local Notation pullG := (@SmoothFormPullback.operator R h2 n q m V W hV hW g hGImage hg).

(** Source for [current_composite_image_cutoff]:
    compact target supports admit one genuine
    intermediate cutoff test agreeing with g#phi
    near the whole original f(spt T),
    supporting composition in Federer 4.1.7,
    p. 359. No cancellation-free support
    equality for f#T is assumed. *)
Theorem current_composite_image_cutoff (K:smooth_compact_set hNZ W):
  exists Q:Hom E F,exists O:set Y,@open YT O /\f @` support `<=` O /\O `<=` V /\
    forall phi:E,@smooth_function_support R Z (A_m Z R^o m) NZ hNZ W E ev phi `<=`
      smooth_compact_carrier K->forall y,O y->fv (Q phi) y=gv (pullG phi) y.
Proof.
pose B:set VT:=fS @` setT.
pose BT:topologicalType:=[the topologicalType of set_type B].
pose H:set BT:=(fun y:BT=>gV (set_val y)) @^-1` (set_val @^-1` smooth_compact_carrier K).
have hK:@compact WT (set_val @^-1` smooth_compact_carrier K).
  exact:(@set_type_compact_preimage ZT W (smooth_compact_carrier K)
    (smooth_compact_is_compact K) (smooth_compact_in_domain K)).
have hH:@compact BT H:=properData.2 _ hK.
pose valY:=fun y:BT=>(set_val (set_val y):YT).
have hVal:continuous valY.
  move=>y;exact:(continuous_comp (@set_type_val_continuous VT B y)
    (@set_type_val_continuous YT V (set_val y))).
pose C:set Y:=valY @` H.
have hC:@compact YT C.
  apply:continuous_compact hH;exact:continuous_subspaceT hVal.
have hCV:C `<=` V by move=>y [z _ <-];exact:set_valP (set_val z).
pose L:=@Build_smooth_compact_set R Y NY hNY V C hCV hC.
have hCarrier:f @` support `<=` V.
  move=>y [x hx <-];exact:hFImage x hx.1.
have hLocus y (hy:(f @` support) y) (hKy:smooth_compact_carrier K (g y)):
    smooth_compact_carrier L y.
  have [x hx hFx]:=hy.
  pose z:ST:=exist _ x (mem_set hx).
  have hB:B (fS z) by exists z.
  pose b:BT:=exist _ (fS z) (mem_set hB).
  exists b.
  - change (smooth_compact_carrier K (g (f x)));by rewrite hFx.
  - change (f x=y);exact:hFx.
have [Q [hQC [O [hO [hImage [hOV hAgreement]]]]]]:=
  @smooth_pullback_compact_locus_tests R h2 n q m V W hV hW (f @` support) hCarrier
    g hGImage hg K L hLocus.
exists Q,O;split;first exact:hO.
split;first exact:hImage.
split;[exact:hOV|exact:hAgreement].
Qed.
End CurrentCompositeImageCutoff.
