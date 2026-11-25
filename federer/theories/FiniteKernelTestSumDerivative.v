(** Federer (1969), 4.1.2, p. 348: every
    derivative of the actual finite test sum equals
    the displayed weighted sum of kernel derivatives.
    All functions and derivative operators are abstract
    objects with their original proved evaluation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationUP SmoothGlobalTranslationDerivatives TranslatedKernelTestUP ScalarVectorSmoothDerivativeValue TranslatedKernelTestDerivativeValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FiniteKernelTestSumDerivative.
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


(** Source for [finite_kernel_test_sum_derivative_value]: the
    exact displayed derivative of the tagged finite sum
    in Federer 4.1.2, p. 348, before
    its compact-uniform error is estimated. *)
Theorem finite_kernel_test_sum_derivative_value (I:finType)
    (tag:I->X) (weight:I->R) (y:I->Y) k x (u:{ffun 'I_k->X}):
  @ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY u
    (@D k x (smooth_test_inclusion hE (\sum_i weight i*:B (tag i) (y i))))=
  \sum_i weight i*:
    ((@ContinuousMultilinear.evaluation R k X R^o NX NS hNX hNS u
      (@DS k (x-tag i) f))*:y i).
Proof.
pose H:=hom_comp (@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY u)
  (hom_comp (@D k x) (smooth_test_inclusion hE)).
change (H (\sum_i weight i*:B (tag i) (y i))=
  \sum_i weight i*:
    ((@ContinuousMultilinear.evaluation R k X R^o NX NS hNX hNS u
      (@DS k (x-tag i) f))*:y i)).
rewrite linear_sum; apply:eq_bigr=>i _; rewrite linearZ /=.
change (weight i*:
    (@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY u
      (@D k x (smooth_test_inclusion hE (B (tag i) (y i)))))=
  weight i*:
    ((@ContinuousMultilinear.evaluation R k X R^o NX NS hNX hNS u
      (@DS k (x-tag i) f))*:y i)).
by rewrite (@translated_kernel_test_derivative_value R X Y NX NY hNX hNY
  S sv DS hDS L hL f psi hF E ev hE D hD B hB (tag i) (y i) k x u).
Qed.
End FiniteKernelTestSumDerivative.
