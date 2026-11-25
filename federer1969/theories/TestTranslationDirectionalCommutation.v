(** Federer (1969), 4.1.8, p. 360: parameter derivatives of
    translated tests are translations of their derivatives. The
    proof uses the actual first differential, as constructed for
    the test operators of 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  ContinuousMultilinearSealed SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestEvaluation SmoothGlobalTranslationSealed
  SmoothGlobalTranslationDerivatives SmoothDirectionalDerivativeSealed
  TestDirectionalOperator DistributionDirectionalDerivative TestGlobalTranslation
  TestGlobalTranslationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TestTranslationDirectionalCommutation.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Variable v:X.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Local Notation P := (@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v).
Local Notation hP := (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v).
Local Notation Q := (@distribution_test_directional_derivative R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).

(** Source for [test_translation_directional_commutation]: the
    actual derivative commutes with translation, supporting smooth
    parameter dependence of the slice in Federer 4.1.8, p. 360.
    This identity follows from the already proved smooth
    differential-translation law of 4.1.1, p. 346. *)
Theorem test_translation_directional_commutation c (f:DT):
  Q (A c f)=A c (Q f).
Proof.
have hQ g:inc (Q g)= P (inc g).
  exact:(@test_directional_evaluation R X Y NX NY hNX hNY (fun _=>True)
    hFull E ev hE D hD v P hP g).
have hValues g x:ev (inc (Q g)) x=
    @ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY
      [ffun _:'I_1=>v] (@D 1%N x (inc g)).
  rewrite hQ; exact:(@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY
    (fun _=>True) E ev hE D hD v (inc g) x Logic.I).
apply:(smooth_test_values_extensional hE)=>x _.
change (ev (inc (Q (A c f))) x=ev (inc (A c (Q f))) x).
rewrite hValues (@test_global_translation_values R X Y NX NY hNX hNY E ev hE c (Q f) x) hValues.
rewrite (@test_global_translation_inclusion R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).
by rewrite (@smooth_global_translation_derivatives R X Y NX NY hNX hNY E ev D hD c (L c) (hL c)).
Qed.
End TestTranslationDirectionalCommutation.
