(** Federer (1969), 4.1.7, p. 359:
    (g composed with f)#T=g#(f#T) under
    the single printed properness hypothesis.
    Intermediate compact replacements agree near
    the full f(spt T); the original
    pullback chain rule then compares both
    actual current actions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormOpenPreimage InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingDual
  CurrentCoefficientNorms CurrentSpaces CurrentEvaluation CurrentMapDifferential CurrentProperSupport
  CurrentCompositeProperness CurrentCompositeImageCutoff CurrentPushforwardUP CurrentPushforwardExistence
  CurrentPushforwardSealed CurrentPushforwardSupport SmoothFormPullbackUP SmoothFormPullbackSealed
  SmoothFormPullbackComposition SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardComposition.
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
Local Notation hGFImage := (@current_smooth_composite_image R v n q U V W f g hFImage hGImage).
Local Notation hGF := (@current_smooth_composite_class R v n q U V f g hFImage hf hg).
Hypothesis hpGF:@is_current_proper_on_support R h2 v q m U hU W T (fun x=>g (f x)) hGFImage.
Local Notation properData := (@current_composite_support_properness R h2 v n q m U V W hU
  f g hFImage hGImage hf hg T hpGF).
Local Notation hpF := properData.1.
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hFImage hf hpF).
Local Notation hpG := (@current_composite_pushed_support_proper R h2 v n q m U V W hU hV
  f g hFImage hGImage hf hg T hpGF).
Local Notation E := (@current_smooth_space R h2 q W hW m).
Local Notation F := (@current_smooth_space R h2 n V hV m).
Local Notation G := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 q W hW m).
Local Notation fv := (@current_smooth_value R h2 n V hV m).
Local Notation gv := (@current_smooth_value R h2 v U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 q W hW m).
Local Notation hF := (@current_smooth_space_laws R h2 n V hV m).
Local Notation pullF := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hFImage hf).
Local Notation pullG := (@SmoothFormPullback.operator R h2 n q m V W hV hW g hGImage hg).
Local Notation pullGF := (@SmoothFormPullback.operator R h2 v q m U W hU hW (fun x=>g (f x)) hGFImage hGF).

(** Source for [current_pushforward_composition]:
    (g composed with f)#T=g#(f#T), Federer
    4.1.7, p. 359. Only g composed
    with f restricted to spt T
    is assumed proper. No integration
    representation or normality is imposed. *)
Theorem current_pushforward_composition:
  @CurrentPushforward.value R h2 v q m U W hU hW T (fun x=>g (f x)) hGFImage hGF hpGF=
    @CurrentPushforward.value R h2 n q m V W hV hW S g hGImage hg hpG.
Proof.
apply:(@current_values_extensional R h2 q m W hW)=>phi.
have [K hK]:=smooth_test_support_bound hE phi.
have [Q [O [hO [hImageO [hOV hAgreementG]]]]]:=
  @current_composite_image_cutoff R h2 v n q m U V W hU hV hW f g hFImage hGImage
    hf hg T hpGF K.
pose chi:=Q (smooth_test_inclusion hE phi).
have hChi y (hy:O y):@current_test_value R h2 n V hV m chi y=
    fv (pullG (smooth_test_inclusion hE phi)) y.
  exact:hAgreementG (smooth_test_inclusion hE phi) hK y hy.
have hReplacementG:@is_current_pullback_test_replacement R h2 n q m V W hV hW S g hGImage hg phi chi.
  exists O;split;first exact:hO.
  split.
  - move=>y hy;exact:hImageO y
      (@current_pushforward_support_image R h2 v n m U V hU hV T f hFImage hf hpF y hy).
  - split;[exact:hOV|exact:hChi].
have [psi hReplacementF]:=@current_pushforward_test_replacement_exists R h2 v n m U V hU hV
  T f hFImage hf hpF chi.
have [A [hA [hTA [hAU hAgreementF]]]]:=hReplacementF.
pose B:set X:=[set x|U x /\O (f x)].
have hB:@open (real_norm_metric_space hNX) B.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY U O f
    (norm_class_continuous (hf 0%N)) hO).
have hReplacementGF:@is_current_pullback_test_replacement R h2 v q m U W hU hW T
    (fun x=>g (f x)) hGFImage hGF phi psi.
  exists (A `&` B);split;first exact:openI hA hB.
  split.
  - move=>x hx;split;first exact:hTA x hx.
    split;first exact:hx.1.
    apply:hImageO;by exists x.
  - split;first by move=>x hx;exact:hAU x hx.1.
    move=>x hx.
    pose L:=@current_map_differential R v n U f x.
    have hL:=@current_map_differential_actual R v n U f hf x hx.2.1.
    have hFirst:=@smooth_form_pullback_values R v n m U V F G fv gv f pullF
      (@SmoothFormPullback.laws R h2 v n m U V hU hV f hFImage hf)
      (smooth_test_inclusion hF chi) x L hx.2.1 hL.
    have hSecond:=@smooth_form_pullback_values R v n m U V F G fv gv f pullF
      (@SmoothFormPullback.laws R h2 v n m U V hU hV f hFImage hf)
      (pullG (smooth_test_inclusion hE phi)) x L hx.2.1 hL.
    have hMiddle:=congr1 (@A_m_dual R X Y R^o (hom_as_linear L) m)
      (hChi (f x) hx.2.2).
    have hComposition:=congr1 (fun a:G=>gv a x)
      (@smooth_form_pullback_composition R h2 v n q m U V W hU hV hW f g hFImage hGImage
        hf hg (smooth_test_inclusion hE phi)).
    exact:(eq_trans (hAgreementF x hx.1)
      (eq_trans hFirst (eq_trans hMiddle (eq_trans (esym hSecond) (esym hComposition))))).
have hLeft:=@CurrentPushforward.laws R h2 v q m U W hU hW T (fun x=>g (f x)) hGFImage hGF hpGF
  phi psi hReplacementGF.
have hRight:=eq_trans (@CurrentPushforward.laws R h2 n q m V W hV hW S g hGImage hg hpG
  phi chi hReplacementG) (@CurrentPushforward.laws R h2 v n m U V hU hV T f hFImage hf hpF
    chi psi hReplacementF).
exact:(eq_trans hLeft (esym hRight)).
Qed.
End CurrentPushforwardComposition.
