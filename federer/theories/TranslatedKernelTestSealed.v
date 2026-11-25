(** Federer (1969), 4.1.2, p. 347: opaque
    translated kernel tests. Only the independently specified
    original values are exposed; existence was proved first. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SmoothFunctionSpaceUP SmoothTestSpaces
  TranslatedKernelTestUP TranslatedKernelTestExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type TranslatedKernelTestSignature.
(** Source for [value]: the actual kernel tests defining
    the dual density in Federer 4.1.2, p. 347. *)
Parameter value:forall (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (psi:R_n R n->R),
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) (fun _=>True) psi ->
  forall r:R,(forall x,r<inner_norm (@euclidean_inner_productP R n) x ->psi x=0) ->
  R_n R n->Hom Y (smooth_test_space hE).
(** Source for [laws]: the selected tests have exactly
    the defining values in Federer 4.1.2, p. 347. *)
Parameter laws:forall (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (psi:R_n R n->R)
    (hPsi:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (@scalar_absolute_value_norm R) (fun _=>True) psi)
    (r:R) (hOff:forall x,r<inner_norm (@euclidean_inner_productP R n) x ->psi x=0),
  @is_translated_kernel_tests R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY E ev hE psi
    (@value R n Y NY hNY E ev hE psi hPsi r hOff).
End TranslatedKernelTestSignature.
Module TranslatedKernelTest:TranslatedKernelTestSignature.
(** Source for [value]: hide the proved kernel-test
    witness for Federer 4.1.2, p. 347. *)
Definition value (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (psi:R_n R n->R)
    (hPsi:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (@scalar_absolute_value_norm R) (fun _=>True) psi)
    (r:R) (hOff:forall x,r<inner_norm (@euclidean_inner_productP R n) x ->psi x=0):
  R_n R n->Hom Y (smooth_test_space hE):=
  projT1 (cid (@translated_kernel_tests_exists R n Y NY hNY E ev hE psi hPsi r hOff)).
(** Source for [laws]: the hidden witness satisfies
    the original values in Federer 4.1.2, p. 347. *)
Lemma laws (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (psi:R_n R n->R)
    (hPsi:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (@scalar_absolute_value_norm R) (fun _=>True) psi)
    (r:R) (hOff:forall x,r<inner_norm (@euclidean_inner_productP R n) x ->psi x=0):
  @is_translated_kernel_tests R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY E ev hE psi
    (@value R n Y NY hNY E ev hE psi hPsi r hOff).
Proof.
exact:(projT2 (cid (@translated_kernel_tests_exists R n Y NY hNY E ev hE psi hPsi r hOff))).
Qed.
End TranslatedKernelTest.
