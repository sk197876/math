(** Federer (1969), 4.1.4, p. 349, applying 4.1.2:
    differentiating an actual translated kernel test gives
    the corresponding translated scalar derivative kernel.
    This connects the already proved kernel derivative formula
    to the actual test differentiation operator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormDifferentialUP NormOpenDomainLaws NormDifferentialDirectional NormClassOneUP SmoothGlobalFirstDifferential
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationUP SmoothDirectionalDerivativeUP TestDirectionalOperator
  TranslatedKernelTestUP TranslatedKernelTestDerivativeValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TranslatedKernelTestDirectional.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable S:lmodType R.
Variable sv:S->X->R^o.
Hypothesis hS:is_smooth_function_space hNX hNS (fun _=>True) sv.
Variable DS:forall j,X->Hom S (@ContinuousMultilinear.space R j X R^o NX NS hNX hNS).
Hypothesis hDS:@is_smooth_function_derivatives R X R^o NX NS hNX hNS (fun _=>True) S sv DS.
Variable L:X->Hom S S.
Hypothesis hL:forall c,is_smooth_global_translation sv c (L c).
Variable s:S.
Variable psi:X->R.
Hypothesis hF:forall x,sv s x=psi x.
Variable G:X->Hom X R^o.
Hypothesis hG:forall x,has_norm_differential NX NS (fun _=>True) psi x (G x).
Variable v:X.
Variable theta:X->R.
Hypothesis hTheta:forall x,G x v=theta x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable B C:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y NX NY hNX hNY E ev hE psi B.
Hypothesis hC:@is_translated_kernel_tests R X Y NX NY hNX hNY E ev hE theta C.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY (fun _=>True) E ev D v P.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).

(** Source for [translated_kernel_test_directional_derivative]:
    the actual D_v[psi(x-z)y] equals theta(x-z)y, where
    theta=D_v psi, the kernel-test differentiation used to
    prove D_j g_e=0 in Federer 4.1.4, p. 349. *)
Theorem translated_kernel_test_directional_derivative z y:
  @test_directional_operator R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v P hP (B z y)=C z y.
Proof.
have hRaw:sv s=psi by apply:funext=>x; exact:hF.
have hFirst:=@smooth_global_first_differential_class_one R X R^o NX NS hNX hNS S sv hS DS hDS s.
have hSame x:@smooth_global_first_differential R X R^o NX NS hNX hNS S DS s x=G x.
  have hActual:=@norm_class_one_differential R X R^o NX NS (fun _=>True) (sv s)
    (@smooth_global_first_differential R X R^o NX NS hNX hNS S DS s) hFirst x Logic.I.
  rewrite hRaw in hActual.
  exact:(norm_differential_unique hNX hNS hActual (@hG x)).
apply:(smooth_test_values_extensional hE)=>x _.
change (ev (smooth_test_inclusion hE
  (@test_directional_operator R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v P hP (B z y))) x=
  smooth_test_value hE (C z y) x).
rewrite test_directional_evaluation (@hP _ _ Logic.I) hC.
have hDeriv:=@translated_kernel_test_derivative_value R X Y NX NY hNX hNY
  S sv DS hDS L hL s psi hF E ev hE D hD B hB z y 1%N x [ffun _:'I_1=>v].
rewrite hDeriv.
have hScalar:@ContinuousMultilinear.evaluation R 1%N X R^o NX NS hNX hNS
    [ffun _:'I_1=>v] (@DS 1%N (x-z) s)=theta (x-z).
  change (@smooth_global_first_differential R X R^o NX NS hNX hNS S DS s (x-z) v=theta (x-z)).
  by rewrite hSame hTheta.
by rewrite hScalar.
Qed.
End TranslatedKernelTestDirectional.
