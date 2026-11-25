(** Federer (1969), 4.1.9, p. 363: the original
    endpoint pullbacks are the slice pullbacks.
    Equal maps on U have equal actual differentials
    there, by 3.1.1, pp. 209–210. Use the
    public pullback value law of 4.1.6, p. 353. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingDual CurrentSpaces
  CurrentMapDifferential CurrentClassOneMapDifferential SmoothFormPullbackUP SmoothFormPullbackSealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPullbackMapAgreement.
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
Variables (f g:X->Y).
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Local Notation EU := (@current_smooth_space R h2 n U hU m).
Local Notation EV := (@current_smooth_space R h2 nu V hV m).
Local Notation vu := (@current_smooth_value R h2 n U hU m).
Local Notation vv := (@current_smooth_value R h2 nu V hV m).
Local Notation pullF := (@SmoothFormPullback.operator R h2 n nu m U V hU hV f hFImage hf).
Local Notation pullG := (@SmoothFormPullback.operator R h2 n nu m U V hU hV g hGImage hg).

(** Source for [current_pullback_map_agreement]: f#phi=
    g#phi for every original smooth form when f=g
    on U, supporting the endpoint terms in
    Federer 4.1.9, p. 363. The total map
    representatives may differ outside U. *)
Theorem current_pullback_map_agreement:
  (forall x,U x->f x=g x)->forall phi:EV,pullF phi=pullG phi.
Proof.
move=>hFG phi.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n U hU m))=>x hx.
pose L:=@current_map_differential R n nu U f x.
have hL:=@current_map_differential_actual R n nu U f hf x hx.
have hDifferential:=@current_map_differential_domain_agreement R n nu U f g hFG (hf 1%N) x hx.
have hM:=@current_map_differential_actual R n nu U g hg x hx.
rewrite -hDifferential in hM.
have hFirst:=@smooth_form_pullback_values R n nu m U V EV EU vv vu f pullF
  (@SmoothFormPullback.laws R h2 n nu m U V hU hV f hFImage hf) phi x L hx hL.
have hSecond:=@smooth_form_pullback_values R n nu m U V EV EU vv vu g pullG
  (@SmoothFormPullback.laws R h2 n nu m U V hU hV g hGImage hg) phi x L hx hM.
by rewrite hFirst hSecond (hFG x hx).
Qed.
End CurrentPullbackMapAgreement.
