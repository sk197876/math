(** Federer (1969), 4.1.2, p. 347: opaque
    original smoothing operators on E(R^n,Y).
    Their exact integral specification and proved
    existence precede this seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothingKernelUP SmoothingDilationUP SmoothSmoothingFamilyUP SmoothSmoothingFamilyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SmoothSmoothingFamilySignature.
(** Source for [value]: the original family of
    linear smoothing operators, Federer 4.1.2, p. 347. *)
Parameter value:forall (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family),R->Hom E E.
(** Source for [laws]: every positive-scale value is
    the independently specified original convolution,
    Federer 4.1.2, p. 347. *)
Parameter laws:forall (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family),
  is_smooth_smoothing_family hNY ev family (@value R n Y NY hNY hY hSep E ev hE phi hPhi family hFamily).
End SmoothSmoothingFamilySignature.
Module SmoothSmoothingFamily:SmoothSmoothingFamilySignature.
(** Source for [value]: choose the already proved
    smoothing family before hiding its representation,
    Federer 4.1.2, p. 347. *)
Definition value (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family):R->Hom E E:=
  projT1 (cid (@smooth_smoothing_family_exists R n Y NY hNY hY hSep E ev hE phi hPhi family hFamily)).
(** Source for [laws]: the hidden witness satisfies
    exactly the original integral values,
    Federer 4.1.2, p. 347. *)
Lemma laws (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family):
  is_smooth_smoothing_family hNY ev family (@value R n Y NY hNY hY hSep E ev hE phi hPhi family hFamily).
Proof. exact:(projT2 (cid (@smooth_smoothing_family_exists R n Y NY hNY hY hSep E ev hE phi hPhi family hFamily))). Qed.
End SmoothSmoothingFamily.
