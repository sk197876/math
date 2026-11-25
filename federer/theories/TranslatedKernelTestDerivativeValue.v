(** Federer (1969), 4.1.2, p. 348: every
    original derivative of a translated kernel test is
    the translated scalar kernel derivative times its vector
    coefficient. This gives the exact differentiated finite sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationUP SmoothGlobalTranslationDerivatives TranslatedKernelTestUP ScalarVectorSmoothDerivativeValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TranslatedKernelTestDerivativeValue.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable S:lmodType R.
Variable sv:S->X->R^o.
Variable DS:forall j,X->Hom S (@ContinuousMultilinear.space R j X R^o NX NS hNX hNS).
Hypothesis hDS:@is_smooth_function_derivatives R X R^o NX NS hNX hNS (fun _=>True) S sv DS.
Variable L:X->Hom S S.
Hypothesis hL:forall c,is_smooth_global_translation sv c (L c).
Variable f:S.
Variable psi:X->R.
Hypothesis hF:forall x,sv f x=psi x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Variable B:X->Hom Y (smooth_test_space hE).
Hypothesis hB:@is_translated_kernel_tests R X Y NX NY hNX hNY E ev hE psi B.

(** Source for [translated_kernel_test_derivative_value]: the exact
    identity used in the displayed D^alpha psi sum
    in Federer 4.1.2, p. 348. It
    holds for every original full derivative evaluation. *)
Theorem translated_kernel_test_derivative_value z y k x (u:{ffun 'I_k->X}):
  @ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY u
      (@D k x (smooth_test_inclusion hE (B z y)))=
    (@ContinuousMultilinear.evaluation R k X R^o NX NS hNX hNS u
      (@DS k (x-z) f))*:y.
Proof.
have hG t:=@smooth_derivative_exact R X R^o NX NS hNX hNS (fun _=>True)
  S sv DS hDS k (L (-z) f) t Logic.I.
have hValue t:ev (smooth_test_inclusion hE (B z y)) t=sv (L (-z) f) t*:y.
  change (smooth_test_value hE (B z y) t=sv (L (-z) f) t*:y).
  by rewrite hB (hL (-z) f t) hF.
have h:=@scalar_vector_smooth_derivative_value R X Y NX NY hNX hNY E ev D hD
  (sv (L (-z) f)) k (fun t=>@DS k t (L (-z) f)) y
  (smooth_test_inclusion hE (B z y)) hG hValue x u.
rewrite (@smooth_global_translation_derivatives R X R^o NX NS hNX hNS S sv DS hDS
  (-z) (L (-z)) (hL (-z))) in h.
exact h.
Qed.
End TranslatedKernelTestDerivativeValue.
