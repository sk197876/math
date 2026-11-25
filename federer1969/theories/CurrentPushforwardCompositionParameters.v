(** Federer (1969), 4.1.11, p. 365: apply the preceding
    proper pushforward composition to the original insertion and
    endpoint maps. This supporting lemma accepts any admissible
    properness proofs and uses the public composition and
    current-congruence laws of 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentProperSupport
  SmoothFormPullbackComposition CurrentCompositeProperness CurrentPushforwardSealed
  CurrentPushforwardCongruence CurrentPushforwardComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPushforwardCompositionParameters.
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
Hypothesis hpF:@is_current_proper_on_support R h2 v n m U hU V T f hFImage.
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV
  T f hFImage hf hpF).
Hypothesis hpG:@is_current_proper_on_support R h2 n q m V hV W S g hGImage.
Local Notation OldFProper := (@current_composite_support_properness R h2 v n q m U V W hU
  f g hFImage hGImage hf hg T hpGF).1.
Local Notation OldS := (@CurrentPushforward.value R h2 v n m U V hU hV
  T f hFImage hf OldFProper).
Local Notation OldGProper := (@current_composite_pushed_support_proper R h2 v n q m U V W hU hV
  f g hFImage hGImage hf hg T hpGF).

(** Source for [current_pushforward_composition_parameters]:
    (g composed with f)#T=g#(f#T), with any properness witnesses
    on the two separate maps. This is proof-parameter bookkeeping
    for the two endpoint identities in Federer 4.1.11, p. 365;
    the original preceding composition theorem is reused. *)
Theorem current_pushforward_composition_parameters:
  @CurrentPushforward.value R h2 v q m U W hU hW T
    (fun x=>g (f x)) hGFImage hGF hpGF=
  @CurrentPushforward.value R h2 n q m V W hV hW S
    g hGImage hg hpG.
Proof.
have hFirst:OldS=S:=@current_pushforward_current_congruence R h2 v n m U V hU hV
  f hFImage hf T T OldFProper hpF (erefl T).
have hSecond:=@current_pushforward_current_congruence R h2 n q m V W hV hW
  g hGImage hg OldS S OldGProper hpG hFirst.
exact:(eq_trans (@current_pushforward_composition R h2 v n q m U V W hU hV hW
  f g hFImage hGImage hf hg T hpGF) hSecond).
Qed.
End CurrentPushforwardCompositionParameters.
