(** Federer (1969), 4.1.14, p. 371: the
    local Lipschitz image extends the preceding smooth
    support-proper image. Use one original admissible
    compact scalar cutoff. Its compact flat image has
    the old smooth value, while the remainder has
    support avoiding the target test's inverse image.
    No nonsmooth pullback or additional mass is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero LipschitzUP
  SmoothCompactSet CurrentSpaces CurrentEvaluation CurrentContraction CurrentContractionSupport
  CurrentScalarPlateau CurrentSupportGeometry CurrentSupportLinearUnion
  CurrentSupportAgreement CurrentPointEvaluation CurrentProperSupport
  CurrentProperSupportRestriction CurrentProperSupportLinear
  CurrentCommonPushforwardCutoff CurrentPushforwardSealed CurrentPushforwardSupport
  CurrentPushforwardLinear CurrentPushforwardCongruence CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra SmoothTestSpaces
  FlatCurrentsUP CurrentLipschitzCompactImage CurrentLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardUP CurrentFlatLipschitzPushforwardSealed
  CurrentCompactLipschitzPushforwardSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzImageSmoothAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hQ:@is_current_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal T Q.
Local Notation actionU := (@current_value R h2 n U hU m).
Local Notation actionV := (@current_value R h2 nu V hV m).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation testSupport := (@current_test_support R h2 n m U hU).
Local Notation targetSupport := (@current_test_support R h2 nu m V hV).
Local Notation hScalar := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation inc := (smooth_test_inclusion hScalar).
Local Notation scalar := (@current_test_value R h2 n U hU 0%N).
Local Notation contract gamma := (@current_contraction R h2 n 0%N m U hU (inc gamma)).
Local Notation Global := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImage hLocal).
Local Notation OldPush S hp := (@CurrentPushforward.value R h2 n nu m
  U V hU hV S f hImage hf hp).

(** Source for [current_lipschitz_image_smooth_agreement]:
    every local image candidate equals the original
    smooth pushforward when f is smooth, among the
    basic formal properties of Federer 4.1.14, p. 371.
    T retains only original local flatness and support
    properness. Neither normality nor finite mass nor
    compact support of T is an extra premise. *)
Theorem current_lipschitz_image_smooth_agreement:
  Q=OldPush T hProper.
Proof.
apply:(@current_values_extensional R h2 nu m V hV)=>phi.
have[gamma hPlateau]:=@current_common_pushforward_cutoff R h2 n nu m
  U V hU hV f hImage T T hProper hProper phi.
have hGamma:@is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV
    T f phi gamma.
  move=>x hx hPhi;exact:hPlateau x (or_introl hx) hPhi.
pose S:=contract gamma T.
pose hSFlat:=@hT gamma.
have[K hK]:=hSFlat.
pose hCompactS:=@flat_supported_current_compact R h2 n m U hU K S hK.
pose hSProper:=@current_compact_map_proper R h2 n nu m U V hU S f hImage
  (norm_class_continuous (@hf 0%N)) hCompactS.
have hPoint:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U V hU hV f hImage hLocal S hSFlat).2 K hK.
have hSmooth:Global S hSFlat=OldPush S hSProper.
  exact:(@current_compact_lipschitz_image_smooth R h2 n nu m U V hU hV
    f hImage hLocal K S hK hf (Global S hSFlat) hPoint).
pose P:=T-S.
have hSupportS:support S `<=` support T.
  exact:(@current_contraction_support_subset R h2 n 0%N m U hU (inc gamma) T).
have hForm:P=(-1:R)*:S+T by rewrite /P scaleN1r addrC.
have hSupportP:support P `<=` support T.
  move=>x hx.
  have hUnion:@current_support R h2 n U hU m ((-1:R)*:S+T) x.
    by rewrite -hForm.
  case:(@current_support_linear_union R h2 n m U hU (-1:R) S T x hUnion)=>hPointX.
  - exact:hSupportS x hPointX.
  - exact:hPointX.
pose W:=@interior (real_norm_metric_space hNX)
  [set x|scalar gamma x=@zero_form R X R^o 1].
have hW:@open (real_norm_metric_space hNX) W:=open_interior _.
have hOne:forall x,W x->@current_smooth_value R h2 n U hU 0%N (inc gamma) x=
    @zero_form R X R^o 1.
  move=>x hx;exact:interior_subset hx.
have hAgree:forall psi:@current_test_space R h2 n U hU m,
    testSupport psi `<=` W->actionU T psi=actionU S psi.
  move=>psi hPsi;rewrite /S current_contraction_evaluation.
  by rewrite (@current_scalar_test_local_plateau R h2 n m U hU W
    (inc gamma) hOne psi hPsi).
have hOutside:=@current_support_difference_agreement R h2 n m U hU T S W hW hAgree.
have hAvoid:forall x,support P x->~targetSupport phi (f x).
  move=>x hx hPhi.
  exact:((hOutside x hx).2 (@hGamma x (hSupportP x hx) hPhi)).
pose hPProper:=@current_proper_smaller_support R h2 n nu U hU V f hImage
  m m T P hSupportP hProper.
have hAvoidImage:forall y,@current_support R h2 nu V hV m (OldPush P hPProper) y->
    ~targetSupport phi y.
  move=>y hy.
  have[x hx <-]:=@current_pushforward_support_image R h2 n nu m U V hU hV
    P f hImage hf hPProper y hy.
  exact:hAvoid x hx.
have hZero:=@current_test_disjoint_support_zero R h2 nu m V hV
  (OldPush P hPProper) phi hAvoidImage.
pose hSumProper:=@current_proper_support_linear R h2 n nu m U hU V f hImage
  (1:R) P S hPProper hSProper.
have hSum:(1:R)*:P+S=T by rewrite scale1r /P subrK.
have hPushSum:=@current_pushforward_current_congruence R h2 n nu m U V hU hV
  f hImage hf ((1:R)*:P+S) T hSumProper hProper hSum.
have hLinear:=@current_pushforward_linear R h2 n nu m U V hU hV f hImage hf
  (1:R) P S hPProper hSProper hSumProper.
rewrite hPushSum scale1r in hLinear.
pose E:=@current_point_evaluation R h2 nu m V hV phi.
have hValue:=congr1 E hLinear.
have hZeroE:E (OldPush P hPProper)=0:=hZero.
rewrite (linD (hom_linear E)) hZeroE add0r in hValue.
have hQValue:=(proj2 hQ) phi gamma hSFlat hGamma.
rewrite hSmooth in hQValue.
exact:(eq_trans hQValue (esym hValue)).
Qed.
End CurrentLipschitzImageSmoothAgreement.
