(** Federer (1969), 4.1.19, p. 377, using
    4.1.2, p. 348: the first derivative of
    a translated kernel test is its actual scalar
    differential times the fixed coefficient. Reuse the
    proved higher kernel-test evaluation law. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormOpenDomainLaws NormClassOneUP NormRegularity ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionSpaceSealed SmoothFunctionDerivativesUP
  SmoothFunctionDerivativesSealed SmoothGlobalTranslationUP SmoothGlobalTranslationSealed
  SmoothGlobalFirstDifferential SmoothTestSpaces SmoothTestEvaluation
  TranslatedKernelTestUP TranslatedKernelTestDerivativeValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section KernelFirstDerivative.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t : R^o => `|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hNX hNY Full ev.
Variable D : forall k, X -> Hom E
  (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Hypothesis hD : @is_smooth_function_derivatives R X Y NX NY hNX hNY
  Full E ev D.
Variable kernel : X -> R.
Hypothesis hKernel : norm_class_all_orders hNX hNS Full kernel.
Variable G : X -> Hom X R^o.
Hypothesis hG : forall x, has_norm_differential NX NS Full kernel x (G x).
Variable B : X -> Hom Y (smooth_test_space hE).
Hypothesis hB : @is_translated_kernel_tests R X Y NX NY hNX hNY E ev hE kernel B.

(** Source for [translated_kernel_first_derivative_value]:
    the exact first derivative of the kernel
    test used in the smoothing criterion of
    Federer 4.1.19, p. 377. The
    supplied scalar G is identified with the old
    actual derivative by uniqueness, not added as
    a condition on the original measurable form. *)
Theorem translated_kernel_first_derivative_value z y x v :
  @ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY
    [ffun _ : 'I_1 => v] (@D 1%N x (smooth_test_inclusion hE (B z y)))=
    (G (x-z) v)*:y.
Proof.
pose S := @SmoothFunctionSpace.space R X R^o NX NS hNX hNS Full hFull.
pose sv := @SmoothFunctionSpace.value R X R^o NX NS hNX hNS Full hFull.
pose hS := @SmoothFunctionSpace.laws R X R^o NX NS hNX hNS Full hFull.
pose DS := @SmoothFunctionDerivatives.operators R X R^o NX NS hNX hNS Full S sv hS.
pose hDS := @SmoothFunctionDerivatives.laws R X R^o NX NS hNX hNS Full S sv hS.
pose L := @SmoothGlobalTranslation.operator R X R^o NX NS hNX hNS S sv hS.
have hL c := @SmoothGlobalTranslation.laws R X R^o NX NS hNX hNS S sv hS c.
have [s hSValue] := @smooth_function_evaluation_surjective R X R^o NX NS hNX hNS
  Full S sv hS kernel hKernel.
have hValue t : sv s t=kernel t := hSValue t Logic.I.
have hRaw : sv s=kernel by apply: funext=> t; exact: hValue.
have hFirst := @smooth_global_first_differential_class_one R X R^o NX NS hNX hNS
  S sv hS DS hDS s.
have hSame t : @smooth_global_first_differential R X R^o NX NS hNX hNS
    S DS s t=G t.
  have hActual := @norm_class_one_differential R X R^o NX NS Full (sv s)
    (@smooth_global_first_differential R X R^o NX NS hNX hNS S DS s)
    hFirst t Logic.I.
  rewrite hRaw in hActual.
  exact: (norm_differential_unique hNX hNS hActual (@hG t)).
have hDerivative := @translated_kernel_test_derivative_value R X Y NX NY hNX hNY
  S sv DS hDS L hL s kernel hValue E ev hE D hD B hB z y 1%N x
  [ffun _ : 'I_1 => v].
rewrite hDerivative.
change ((@smooth_global_first_differential R X R^o NX NS hNX hNS S DS s (x-z) v)*:y=
  (G (x-z) v)*:y).
by rewrite hSame.
Qed.
End KernelFirstDerivative.
