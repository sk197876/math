(** Federer (1969), 4.1.3, p. 348: zero-dimensional
    boundary regressions. The empty coordinate product is one,
    and the actual opaque tensor map recovers every target
    vector as a constant test on the compact source R^0. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP TensorFamilyUP RealNormUP GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SmoothFunctionSpaceUP SmoothTestSpaces
  TensorTestDensity SmoothTestEvaluation TestTensorMapUP TestTensorMapSealed SeparatedKernelSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [separated_zero_source_kernel_regression]: in
    dimension zero the actual separated kernel has value one;
    this verifies the empty-product endpoint of Federer 4.1.3,
    p. 348, against the original unit-mass convention. *)
Theorem separated_zero_source_kernel_regression (R:realType) (A:lmodType R)
    (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av) (x:R_n R 0):
  \prod_(i:'I_0) smooth_test_value hA (@SeparatedKernel.factor R 0 A av hA) (x i)= 1.
Proof. exact:big_ord0. Qed.

(** Source for [tensor_zero_source_evaluation_regression]: the
    actual canonical map sends the empty scalar tensor with y
    to the constant y test on R^0, supporting the full target
    generality and dimension-zero endpoint of Federer 4.1.3,
    p. 348. *)
Theorem tensor_zero_source_evaluation_regression (R:realType) (A:lmodType R)
    (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R 0->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R 0))
      hNY (fun _=>True) ev) (T W:lmodType R)
    (mu:{dffun forall i:'I_0,smooth_test_space hA}->T) (nu:T->Y->W)
    (hT:is_tensor_product_family mu) (hW:is_tensor_product nu):
  forall f y x,
    smooth_test_value hE (@TestTensorMap.value R 0 A av hA Y NY hNY E ev hE T W mu nu hT hW
      (nu (mu f) y)) x=y.
Proof.
move=>f y x.
have h:=@TestTensorMap.laws R 0 A av hA Y NY hNY E ev hE T W mu nu hT hW f y x.
by rewrite big_ord0 scale1r in h.
Qed.
