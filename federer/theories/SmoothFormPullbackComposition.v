(** Federer (1969), 4.1.7, p. 359:
    composition of actual smooth pullbacks is
    the preceding 4.1.6 chain rule, p. 355.
    Both smooth maps retain their original
    open domains. All pointwise differentials
    come from the sealed original Df. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingDual
  DifferentialFormPullbackUP DifferentialFormPullbackLaws CurrentSpaces CurrentMapDifferential
  SmoothFunctionSpaceLaws SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothFormPullbackComposition.
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
Variables (U:X->Prop) (V:Y->Prop) (W:Z->Prop).
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

(** Source for [current_smooth_composite_image]:
    the actual composite maps U into W,
    supporting Federer 4.1.7, p. 359. *)
Lemma current_smooth_composite_image:forall x,U x->W (g (f x)).
Proof. move=>x hx;exact:hGImage (f x) (hFImage x hx). Qed.

(** Source for [current_smooth_composite_class]:
    the original composite is smooth by
    3.1.11, pp. 221–222, supporting composition
    in Federer 4.1.7, p. 359. *)
Lemma current_smooth_composite_class:norm_class_all_orders hNX hNZ U (fun x=>g (f x)).
Proof.
move=>k;exact:(@norm_class_compose_on R X Y Z NX NY NZ hNX hNY hNZ U V f g k
  hFImage (hf k) (hg k)).
Qed.
Local Notation E := (@current_smooth_space R h2 q W hW m).
Local Notation F := (@current_smooth_space R h2 n V hV m).
Local Notation G := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 q W hW m).
Local Notation fv := (@current_smooth_value R h2 n V hV m).
Local Notation gv := (@current_smooth_value R h2 v U hU m).
Local Notation pullF := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hFImage hf).
Local Notation pullG := (@SmoothFormPullback.operator R h2 n q m V W hV hW g hGImage hg).
Local Notation pullGF := (@SmoothFormPullback.operator R h2 v q m U W hU hW (fun x=>g (f x))
  current_smooth_composite_image current_smooth_composite_class).

(** Source for [smooth_form_pullback_composition]:
    (g composed with f)#phi=f#(g#phi)
    in the actual original smooth spaces,
    supporting Federer 4.1.7, p. 359,
    by the final paragraph of 4.1.6,
    p. 355. No composition law is
    assumed in either operator seal. *)
Theorem smooth_form_pullback_composition (phi:E):pullGF phi=pullF (pullG phi).
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 v U hU m))=>x hx.
pose L:=@current_map_differential R v n U f x.
pose M:=@current_map_differential R n q V g (f x).
have hL:=@current_map_differential_actual R v n U f hf x hx.
have hM:=@current_map_differential_actual R n q V g hg (f x) (hFImage x hx).
have hGValue:=@smooth_form_pullback_values R n q m V W E F ev fv g pullG
  (@SmoothFormPullback.laws R h2 n q m V W hV hW g hGImage hg) phi (f x) M
  (hFImage x hx) hM.
have hFValue:=@smooth_form_pullback_values R v n m U V F G fv gv f pullF
  (@SmoothFormPullback.laws R h2 v n m U V hU hV f hFImage hf) (pullG phi) x L hx hL.
have hComposite:=@differential_form_pullback_composition R X Y Z R^o NX NY NZ hNX hNY hNZ
  U V W f g m (ev phi) x L M hFImage (hGImage (f x) (hFImage x hx)) hL hM.
have hActual:=@SmoothFormPullback.laws R h2 v q m U W hU hW (fun x=>g (f x))
  current_smooth_composite_image current_smooth_composite_class phi x hx.
have hValue:=differential_form_pullback_unique hNX hNZ hActual hComposite.
by rewrite hValue hFValue hGValue.
Qed.
End SmoothFormPullbackComposition.
