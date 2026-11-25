(** Federer (1969), 4.1.2, p. 347: differentiating
    an actual translated scalar kernel gives the
    original differential at the shifted point.
    The translation and directional operators remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneNormalization
  ContinuousMultilinearSealed SmoothFunctionDerivativesUP SmoothGlobalTranslationUP
  SmoothDirectionalDerivativeUP SmoothDirectionalOrdinary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [smooth_translated_ordinary_evaluation]: the actual
    scalar derivative in the displayed formula for
    g_epsilon in Federer 4.1.2, p. 347. *)
Theorem smooth_translated_ordinary_evaluation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->X->Y)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D)
    (L:X->Hom E E) (hL:forall c,is_smooth_global_translation ev c (L c))
    v (P:Hom E E)
    (hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY (fun _=>True) E ev D v P)
    (f:E) (G:X->Hom X Y):
  (forall x,has_norm_differential NX NY (fun _=>True) (ev f) x (G x)) ->
  forall c x,ev (P (L c f)) x=G (x+c) v.
Proof.
move=>hG c x.
have hAt:has_norm_differential NX NY (fun _=>True) (ev f) (c+x) (G (x+c)).
  rewrite addrC; exact:hG.
have hTranslated:=@norm_differential_translate R X Y NX NY (fun _=>True) (ev f)
  c x 0 (G (x+c)) hAt.
have hFunction:(fun t=>ev f (c+t)-0)=ev (L c f).
  apply:funext=>t; by rewrite subr0 (hL c f t) addrC.
rewrite hFunction in hTranslated.
exact:(@smooth_directional_ordinary_evaluation R X Y NX NY hNX hNY (fun _=>True)
  E ev D hD v P hP (L c f) x (G (x+c)) Logic.I hTranslated).
Qed.
