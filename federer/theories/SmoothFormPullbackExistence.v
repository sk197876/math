(** Federer (1969), 4.1.7, p. 359:
    the original smooth pullback exists
    as a linear map between the
    actual original smooth form spaces.
    The coordinate proof establishes smoothness;
    only the public representation laws
    choose its smooth-space representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional NormClassOneUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingDual DifferentialFormPullbackUP CurrentCoefficientNorms CurrentSpaces CurrentPullbackClass SmoothFormPullbackUP
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothFormPullbackExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation E := (@current_smooth_space R h2 n V hV m).
Local Notation F := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.

(** Source for [smooth_form_pullback_member_exists]:
    each original smooth form has
    a genuine smooth pullback, supporting
    Federer 4.1.7, p. 359.
    The original actual differential is
    retained in the independent graph. *)
Lemma smooth_form_pullback_member_exists (phi:E):
  exists g:F,forall x,U x->has_differential_form_pullback NX NY U V f (ev phi) x (fv g x).
Proof.
have [D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 (hf 1%N).
have hActual (x:X) (hx:U x):=norm_class_one_differential hD hx.
have hClass:=@current_smooth_pullback_class R h2 v n m U V hU f D hActual hImage hf
  (ev phi) (smooth_function_evaluation_smooth hE phi).
have [g hg]:=smooth_function_evaluation_surjective hF hClass.
exists g=>x hx;split;first exact:hImage x hx.
exists (D x);split;[exact:hActual x hx|exact:hg x hx].
Qed.

(** Source for [smooth_form_pullback_exists]:
    a linear map realises the independently
    specified original smooth pullback, supporting
    Federer 4.1.7, p. 359.
    Its private representatives are hidden
    by the subsequent opaque seal. *)
Theorem smooth_form_pullback_exists:
  exists P:Hom E F,is_smooth_form_pullback U V ev fv f P.
Proof.
pose member phi:=projT1 (cid (smooth_form_pullback_member_exists phi)).
have hMember phi x hx:=projT2 (cid (smooth_form_pullback_member_exists phi)) x hx.
have hLinear:linear member.
  move=>c phi psi;apply:(smooth_function_extensional hF)=>x hx.
  have [_ [D [hD hValue]]]:=hMember phi x hx.
  have hPsi:=hMember psi x hx.
  have hSum:=hMember (c*:phi+psi) x hx.
  have [hImageX [A [hA hValueSum]]]:=hSum.
  have [_ [B [hB hValuePsi]]]:=hPsi.
  have hDA:=norm_differential_unique hNX hNY hA hD.
  have hDB:=norm_differential_unique hNX hNY hB hD.
  rewrite hDA in hValueSum;rewrite hDB in hValuePsi.
  rewrite hValueSum (smooth_function_add_value hF) (smooth_function_scale_value hF)
    hValue hValuePsi (smooth_function_add_value hE) (smooth_function_scale_value hE).
  by rewrite ?linearD ?linearZ.
exists (@HomMap R E F member (introT (asboolP _) hLinear)).
exact:hMember.
Qed.
End SmoothFormPullbackExistence.
