(** Federer (1969), 4.1.2, p. 347: opaque positive-scale
    smoothing of actual distributions. The implementation is selected
    only after the complete original existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  NormOpenTopology OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestTopology ContinuousRealDual SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP TestSmoothingFamilyUP SmoothedDistributionFamilyUP SmoothedDistributionFamilyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SmoothedDistributionFamilySignature.
(** Source for [value]: the family T_epsilon, Federer 4.1.2, p. 347. *)
Parameter value:forall (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (D:forall j,R_n R n->Hom E (@ContinuousMultilinear.space R j (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY))
    (hD:@is_smooth_function_derivatives R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev D)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P)
    (Q:R->Hom (smooth_test_space hE) (smooth_test_space hE))
    (hQ:@is_test_smoothing_family R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n))
      NY (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev hE P Q)
    (T:Hom (smooth_test_space hE) R^o)
    (hT:open_family_continuous (smooth_test_opens hE hD) (norm_open_family (@scalar_absolute_value_norm R)) T),R->(@continuous_real_dual_space R (smooth_test_space hE) (smooth_test_opens hE hD)
    (smooth_test_final_topology_laws hE hD).1).
(** Source for [laws]: exact action on every actual test at every positive scale,
    Federer 4.1.2, p. 347. *)
Parameter laws:forall (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (D:forall j,R_n R n->Hom E (@ContinuousMultilinear.space R j (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY))
    (hD:@is_smooth_function_derivatives R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev D)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P)
    (Q:R->Hom (smooth_test_space hE) (smooth_test_space hE))
    (hQ:@is_test_smoothing_family R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n))
      NY (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev hE P Q)
    (T:Hom (smooth_test_space hE) R^o)
    (hT:open_family_continuous (smooth_test_opens hE hD) (norm_open_family (@scalar_absolute_value_norm R)) T),is_smoothed_distribution_family (@continuous_real_dual_evaluation R (smooth_test_space hE) (smooth_test_opens hE hD)
    (smooth_test_final_topology_laws hE hD).1) T Q (@value R n Y NY hNY hY hSep E ev hE D hD phi hPhi family hFamily P hP Q hQ T hT).
End SmoothedDistributionFamilySignature.
Module SmoothedDistributionFamily:SmoothedDistributionFamilySignature.
(** Source for [value]: hide the already proved family, Federer 4.1.2, p. 347. *)
Definition value (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (D:forall j,R_n R n->Hom E (@ContinuousMultilinear.space R j (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY))
    (hD:@is_smooth_function_derivatives R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev D)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P)
    (Q:R->Hom (smooth_test_space hE) (smooth_test_space hE))
    (hQ:@is_test_smoothing_family R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n))
      NY (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev hE P Q)
    (T:Hom (smooth_test_space hE) R^o)
    (hT:open_family_continuous (smooth_test_opens hE hD) (norm_open_family (@scalar_absolute_value_norm R)) T):R->(@continuous_real_dual_space R (smooth_test_space hE) (smooth_test_opens hE hD)
    (smooth_test_final_topology_laws hE hD).1):=
 projT1 (cid (@smoothed_distribution_family_exists R n Y NY hNY hY hSep E ev hE D hD phi hPhi family hFamily P hP Q hQ T hT)).
(** Source for [laws]: the hidden family has precisely the original action,
    Federer 4.1.2, p. 347. *)
Lemma laws (R:realType) n (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (D:forall j,R_n R n->Hom E (@ContinuousMultilinear.space R j (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY))
    (hD:@is_smooth_function_derivatives R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev D)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (P:R->Hom E E) (hP:is_smooth_smoothing_family hNY ev family P)
    (Q:R->Hom (smooth_test_space hE) (smooth_test_space hE))
    (hQ:@is_test_smoothing_family R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n))
      NY (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) E ev hE P Q)
    (T:Hom (smooth_test_space hE) R^o)
    (hT:open_family_continuous (smooth_test_opens hE hD) (norm_open_family (@scalar_absolute_value_norm R)) T):is_smoothed_distribution_family (@continuous_real_dual_evaluation R (smooth_test_space hE) (smooth_test_opens hE hD)
    (smooth_test_final_topology_laws hE hD).1) T Q (@value R n Y NY hNY hY hSep E ev hE D hD phi hPhi family hFamily P hP Q hQ T hT).
Proof. exact:(projT2 (cid (@smoothed_distribution_family_exists R n Y NY hNY hY hSep E ev hE D hD phi hPhi family hFamily P hP Q hQ T hT))). Qed.
End SmoothedDistributionFamily.
