(** Federer (1969), 4.1.2, p. 347: opaque
    smoothing endomorphisms of the original test space.
    Compact support and the independent inclusion
    specification have already been proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothingKernelUP SmoothingDilationUP SmoothSmoothingFamilyUP
  TestSmoothingFamilyUP TestSmoothingFamilyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type TestSmoothingFamilySignature.
(** Source for [value]: the original smoothing
    endomorphism family on D, Federer 4.1.2, p. 347. *)
Parameter value:forall (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P),
  R->Hom (smooth_test_space hE) (smooth_test_space hE).
(** Source for [laws]: exact agreement with
    the original smooth-space convolution after inclusion,
    Federer 4.1.2, p. 347. *)
Parameter laws:forall (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P),
  @is_test_smoothing_family R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev hE P (@value R n Y NY hNY E ev hE phi hPhi family hFamily P hP).
End TestSmoothingFamilySignature.
Module TestSmoothingFamily:TestSmoothingFamilySignature.
(** Source for [value]: select the already proved
    test-space family and hide its representation,
    Federer 4.1.2, p. 347. *)
Definition value (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P):R->Hom (smooth_test_space hE) (smooth_test_space hE):=
  projT1 (cid (@test_smoothing_family_exists R n Y NY hNY E ev hE phi hPhi family hFamily P hP)).
(** Source for [laws]: the hidden family satisfies
    exactly the independently specified original values,
    Federer 4.1.2, p. 347. *)
Lemma laws (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P):
  @is_test_smoothing_family R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev hE P (@value R n Y NY hNY E ev hE phi hPhi family hFamily P hP).
Proof. exact:(projT2 (cid (@test_smoothing_family_exists R n Y NY hNY E ev hE phi hPhi family hFamily P hP))). Qed.
End TestSmoothingFamily.
