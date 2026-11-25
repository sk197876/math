(** Federer (1969), 4.1.9, p. 363: identify the
    original endpoint pushforwards with the fixed-time
    slice pushforwards. The preceding pullback agreement
    gives identical compact-replacement laws for the
    original currents of 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentProperSupport CurrentPushforwardUP
  CurrentPushforwardExistence CurrentPushforwardSealed CurrentPullbackMapAgreement
  SmoothFormPullbackSealed SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPushforwardMapAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R nu)) V y.
Variables f g:X->Y.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFProper:@is_current_proper_on_support R h2 n nu m U hU V T f hFImage.
Hypothesis hGProper:@is_current_proper_on_support R h2 n nu m U hU V T g hGImage.

(** Source for [current_pushforward_map_agreement]: maps
    agreeing on U have equal original pushforwards
    of T, supporting the endpoint identification in
    Federer 4.1.9, p. 363. The defining cutoff
    neighbourhoods and properness domains remain unchanged. *)
Theorem current_pushforward_map_agreement:
  (forall x,U x->f x=g x)->
  @CurrentPushforward.value R h2 n nu m U V hU hV T f hFImage hf hFProper=
    @CurrentPushforward.value R h2 n nu m U V hU hV T g hGImage hg hGProper.
Proof.
move=>hFG.
apply:(@current_pushforward_unique R h2 n nu m U V hU hV T f hFImage hf hFProper).
- exact:(@CurrentPushforward.laws R h2 n nu m U V hU hV T f hFImage hf hFProper).
- move=>phi psi [W [hW [hTW [hWU hAgreement]]]].
  apply:(@CurrentPushforward.laws R h2 n nu m U V hU hV T g hGImage hg hGProper phi psi).
  exists W;split;first exact:hW.
  split;first exact:hTW.
  split;first exact:hWU.
  move=>x hx.
  apply:(eq_trans (hAgreement x hx)).
  exact (congr1 (fun alpha=>@current_smooth_value R h2 n U hU m alpha x)
    (@current_pullback_map_agreement R h2 n nu m U V hU hV f g hFImage hGImage hf hg hFG
      (smooth_test_inclusion (@current_smooth_space_laws R h2 nu V hV m) phi))).
Qed.
End CurrentPushforwardMapAgreement.
