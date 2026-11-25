(** Federer (1969), 4.1.14, p. 371: the
    original locally flat images satisfy (g composed f)#T
    =g#(f#T). Properness of the composite on
    spt T supplies the source and intermediate
    compact cutoffs. Only actual compact image
    composition and the literal local cutoff law
    are used; a nonsmooth cutoff composition is
    never treated as a smooth test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero LipschitzUP MetricLocalLipschitzComposition
  OpenLocalLipschitzCompact SmoothFormPullbackComposition SmoothCompactSet CurrentSpaces CurrentEvaluation CurrentSupportGeometry
  CurrentContraction CurrentContractionSupport CurrentScalarCutoffs CurrentProperSupport
  SmoothTestSpaces SmoothTestEvaluation FlatCurrentsUP FlatCurrentScalarClosure
  CurrentLipschitzPushforwardUP CurrentLipschitzImageSupport
  CurrentLipschitzCompositeProperness CurrentLipschitzImageCutoffContraction
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzComposition CurrentFlatLipschitzCutoffAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzImagesComposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu omega m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R omega).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U:set X) (V:set Y) (W:set Z).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Hypothesis hW:forall z,W z->norm_domain_interior NZ W z.
Variables (f:X->Y) (g:Y->Z).
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall y,V y->W (g y).
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V g.
Local Notation gf:=(fun x=>g (f x)).
Let hGFImage:forall x,U x->W (gf x):=fun x hx=>@hGImage (f x) (@hFImage x hx).
Let hGFLocal:=@metric_local_lipschitz_composition R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (real_norm_metric_space hNZ) U V f g hFImage hFLocal hGLocal.
Local Notation F:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hFImage hFLocal).
Local Notation G:=(@CurrentFlatLipschitzPushforward.value R h2 nu omega m
  V W hV hW g hGImage hGLocal).
Local Notation GF:=(@CurrentFlatLipschitzPushforward.value R h2 n omega m
  U W hU hW gf hGFImage hGFLocal).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProper:@is_current_proper_on_support R h2 n omega m U hU W T gf hGFImage.
Variables (Q:@current_space R h2 nu V hV m)
  (A B:@current_space R h2 omega W hW m).
Hypothesis hQ:@is_current_lipschitz_image R h2 n nu m U V hU hV
  f hFImage hFLocal T Q.
Hypothesis hA:@is_current_lipschitz_image R h2 nu omega m V W hV hW
  g hGImage hGLocal Q A.
Hypothesis hB:@is_current_lipschitz_image R h2 n omega m U W hU hW
  gf hGFImage hGFLocal T B.

(** Source for [current_lipschitz_images_composition]:
    every pair of independently specified original
    local images obeys composition, Federer 4.1.14,
    p. 371. The only properness premise is
    for the composite on the actual spt T.
    Source and intermediate images may be noncompact. *)
Theorem current_lipschitz_images_composition:B=A.
Proof.
pose hf:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hFLocal.
pose hg:=@norm_open_local_lipschitz_class_zero R Y Z NY NZ hNY hNZ V g hV hGLocal.
pose hGFProof:=@current_smooth_composite_image R n nu omega U V W f g hFImage hGImage.
have hGFProofEqual:hGFProof=hGFImage:=Prop_irrelevance _ _.
have hProperOld:@is_current_proper_on_support R h2 n omega m U hU W T gf hGFProof.
  by rewrite hGFProofEqual;exact:hProper.
have hFProper:=(@current_lipschitz_composite_support_properness R h2 n nu omega m
  U V W hU f g hFImage hGImage hf hg T hProperOld).1.
have hQSupport:=@current_lipschitz_image_support R h2 n nu m U V hU hV
  f hFImage hFLocal T hT hFProper Q hQ.
apply:(@current_values_extensional R h2 omega m W hW)=>phi.
have[K hPhi]:=smooth_test_support_bound (@current_smooth_space_laws R h2 omega W hW m) phi.
have[L hL]:=@current_lipschitz_composite_full_image_compact_locus R h2 n nu omega m
  U V W hU f g hFImage hGImage hf T hProperOld K.
have[gamma [O [hO [hLO [hOV hOneGamma]]]]]:=@current_compact_scalar_cutoff R h2 nu V hV L.
have hGammaImage:forall y,(f @` @current_support R h2 n U hU m T) y ->
    @current_test_support R h2 omega m W hW phi (g y) ->
    @interior (real_norm_metric_space hNY)
      [set z|@current_test_value R h2 nu V hV 0%N gamma z=@zero_form R Y R^o 1] y.
  move=>y [x hx <-] hTarget.
  have hLx:smooth_compact_carrier L (f x):=@hL x hx (hPhi _ hTarget).
  have hNear:=open_nbhs_nbhs (conj hO (hLO _ hLx)).
  apply:(filterS _ hNear)=>z hz;exact:hOneGamma z hz.
have[J hGammaSupport]:=smooth_test_support_bound (@current_smooth_space_laws R h2 nu V hV 0%N) gamma.
pose LF:=@current_proper_support_compact_locus R h2 n nu m U hU V
  T f hFImage hFProper J.
pose LGF:=@current_proper_support_compact_locus R h2 n omega m U hU W
  T gf hGFImage hProper K.
pose LSource:=smooth_compact_union LF LGF.
have[delta [O0 [hO0 [hDeltaSource [hO0U hOneDelta]]]]]:=
  @current_compact_scalar_cutoff R h2 n U hU LSource.
have hDeltaPlateau x (hx:smooth_compact_carrier LSource x):
    @interior (real_norm_metric_space hNX)
      [set z|@current_test_value R h2 n U hU 0%N delta z=@zero_form R X R^o 1] x.
  have hNear:=open_nbhs_nbhs (conj hO0 (hDeltaSource x hx)).
  apply:(filterS _ hNear)=>z hz;exact:hOneDelta z hz.
have hDeltaGamma:forall x,@current_support R h2 n U hU m T x ->
    @current_test_support R h2 nu 0%N V hV gamma (f x) ->
    @interior (real_norm_metric_space hNX)
      [set z|@current_test_value R h2 n U hU 0%N delta z=@zero_form R X R^o 1] x.
  move=>x hx hTarget;apply:(@hDeltaPlateau x);left.
  exact:conj hx (hGammaSupport _ hTarget).
have hDeltaComposite:@is_current_lipschitz_pushforward_cutoff R h2 n omega m
    U W hU hW T gf phi delta.
  move=>x hx hTarget;apply:(@hDeltaPlateau x);right;exact:conj hx (hPhi _ hTarget).
pose TD:=@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) delta) T.
pose hTD:=hT delta.
pose FD:=F TD hTD.
pose hFD:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hFImage hFLocal TD hTD).1.
pose QGamma:=@current_contraction R h2 nu 0%N m V hV
  (smooth_test_inclusion (@current_smooth_space_laws R h2 nu V hV 0%N) gamma) Q.
pose FDGamma:=@current_contraction R h2 nu 0%N m V hV
  (smooth_test_inclusion (@current_smooth_space_laws R h2 nu V hV 0%N) gamma) FD.
pose hQGamma:=hQ.1 gamma.
pose hFDGamma:=@flat_current_scalar_multiplier R h2 nu m V hV gamma FD hFD.
have hContraction:QGamma=FDGamma.
  exact:(@current_lipschitz_image_cutoff_contraction R h2 n nu m U V hU hV
    f hFImage hFLocal T hT Q hQ gamma delta hDeltaGamma).
have hCutQ:@is_current_lipschitz_pushforward_cutoff R h2 nu omega m
    V W hV hW Q g phi gamma.
  move=>y hy;exact:(@hGammaImage y (@hQSupport y hy)).
have hCutFD:@is_current_lipschitz_pushforward_cutoff R h2 nu omega m
    V W hV hW FD g phi gamma.
  move=>y hy.
  have[x hx <-]:=@current_flat_lipschitz_pushforward_support R h2 n nu m U V hU hV
    f hFImage hFLocal TD hTD y hy.
  have hxT:=@current_contraction_support_subset R h2 n 0%N m U hU
    (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) delta) T x hx.
  apply:(@hGammaImage (f x));by exists x.
have hActionA:=hA.2 phi gamma hQGamma hCutQ.
have hGammaImages:=@current_flat_lipschitz_pushforward_congruence R h2 nu omega m
  V W hV hW g hGImage hGLocal QGamma FDGamma hQGamma hFDGamma hContraction.
rewrite hGammaImages in hActionA.
have hActionFD:=@current_flat_lipschitz_pushforward_cutoff_action R h2 nu omega m
  V W hV hW g hGImage hGLocal FD hFD phi gamma hFDGamma hCutFD.
rewrite -hActionFD in hActionA.
have hComposition:=@current_flat_lipschitz_pushforward_composition R h2 n nu omega m
  U V W hU hV hW f g hFImage hGImage hFLocal hGLocal TD hTD.
rewrite -hComposition in hActionA.
exact:(eq_trans (hB.2 phi delta hTD hDeltaComposite) (esym hActionA)).
Qed.
End CurrentLipschitzImagesComposition.
