(** Federer (1969), 4.1.1, p. 346: every
    derivative of the translated smooth function
    is the translated original derivative, as
    required by the compact Taylor estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed NormHigherDifferentialUnique
  NormHigherGlobalTranslation SmoothFunctionDerivativesUP SmoothGlobalTranslationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_global_translation_derivatives]: the
    exact derivative-translation identity supporting
    the difference quotient of Federer 4.1.1,
    p. 346. It follows from the original
    recursive differentials, without a new chain rule. *)
Theorem smooth_global_translation_derivatives (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->X->Y)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D)
    c (L:Hom E E):
  is_smooth_global_translation ev c L ->forall f k x,@D k x (L f)=@D k (x+c) f.
Proof.
move=>hL f k x.
pose Z j:=@ContinuousMultilinear.space R j X Y NX NY hNX hNY.
pose ez j:=@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY.
pose ZN j:=@ContinuousMultilinear.norm R j X Y NX NY hNX hNY.
pose hZ j:=@ContinuousMultilinear.laws R j X Y NX NY hNX hNY.
have hShift:=@norm_higher_global_translation R X Y NX NY hNX hNY Z ez ZN hZ (ev f)
  (fun j y=>@D j y f) (fun j y=>@smooth_derivative_exact R X Y NX NY hNX hNY
    (fun _=>True) E ev D hD j f y Logic.I) c k x.
have hValues:(fun y=>ev f (y+c))=ev (L f) by apply:funext=>y; symmetry; exact:hL.
rewrite hValues in hShift.
exact:(norm_higher_differential_unique hNX hNY hZ
  (@smooth_derivative_exact R X Y NX NY hNX hNY (fun _=>True) E ev D hD k (L f) x Logic.I) hShift).
Qed.
