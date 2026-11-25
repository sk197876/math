(** Federer (1969), 4.1.5, pp. 349–350: opaque
    extension of the actual distribution to compact
    continuous vector fields. The independent laws and
    their existence proof precede this sealed choice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionFiniteVariationUP
  DistributionContinuousExtensionUP EuclideanDistributionContinuousExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type DistributionContinuousExtensionSignature.
(** Source for [value]: the original T on compact
    continuous D, Federer 4.1.5, p. 349. *)
Parameter value:forall (R:realType) (n:nat) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (U:set (R_n R n))
    (hU:forall x,U x ->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY U ev)
    (S:Hom (smooth_test_space hE) R^o)
    (hFinite:@is_finite_distribution_variation R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY (smooth_test_space hE) (smooth_test_values_hom hE) S), (R_n R n->Y)->R.
(** Source for [laws]: the actual T is linear,
    extends S and has the original compact uniform
    limit law, Federer 4.1.5, pp. 349–350. *)
Parameter laws:forall (R:realType) (n:nat) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (U:set (R_n R n))
    (hU:forall x,U x ->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY U ev)
    (S:Hom (smooth_test_space hE) R^o)
    (hFinite:@is_finite_distribution_variation R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY (smooth_test_space hE) (smooth_test_values_hom hE) S), @is_distribution_continuous_extension R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY hNY (smooth_test_space hE) (smooth_test_values_hom hE) S
      (@value R n Y NY hNY hY U hU E ev hE S hFinite).
End DistributionContinuousExtensionSignature.
Module DistributionContinuousExtension:DistributionContinuousExtensionSignature.
(** Source for [value]: the hidden proved witness
    of the original extension, Federer 4.1.5, p. 349. *)
Definition value (R:realType) (n:nat) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (U:set (R_n R n))
    (hU:forall x,U x ->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY U ev)
    (S:Hom (smooth_test_space hE) R^o)
    (hFinite:@is_finite_distribution_variation R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY (smooth_test_space hE) (smooth_test_values_hom hE) S):(R_n R n->Y)->R:=
  projT1 (cid (@euclidean_distribution_continuous_extension R n Y NY hNY hY U hU E ev hE S hFinite)).
(** Source for [laws]: the hidden witness satisfies
    only the public original extension laws, Federer
    4.1.5, pp. 349–350. *)
Lemma laws (R:realType) (n:nat) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (U:set (R_n R n))
    (hU:forall x,U x ->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY U ev)
    (S:Hom (smooth_test_space hE) R^o)
    (hFinite:@is_finite_distribution_variation R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY (smooth_test_space hE) (smooth_test_values_hom hE) S):@is_distribution_continuous_extension R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY hNY (smooth_test_space hE) (smooth_test_values_hom hE) S
      (@value R n Y NY hNY hY U hU E ev hE S hFinite).
Proof. exact:(projT2 (cid (@euclidean_distribution_continuous_extension R n Y NY hNY hY U hU E ev hE S hFinite))). Qed.
End DistributionContinuousExtension.
