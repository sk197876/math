(** Federer (1969), 4.1.5, pp. 349–350: the
    original finite gauge on K(U)+ gives a linear
    extension of the actual S to all compact continuous
    vector fields on U. Every approximation and test
    inclusion premise is proved for the actual spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  CompleteMetricUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormEquivalence SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  CompactContinuousDomainFields CompactContinuousTestApproximation SmoothTestCompactContinuous
  DistributionFiniteVariationUP DistributionVariationDomainFinite DistributionContinuousExtensionUP
  DistributionContinuousExtensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distribution_continuous_extension]:
    the original linear extension T in Federer
    4.1.5, pp. 349–350, exists from the literal
    K(U)+ finite-gauge condition. This argument requires
    no separability of the whole dual or extra condition
    on the arbitrary open U. *)
Theorem euclidean_distribution_continuous_extension (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (U:set (R_n R n))
    (hU:forall x,U x ->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY U ev)
    (S:Hom (smooth_test_space hE) R^o):
  @is_finite_distribution_variation R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    U Y NY (smooth_test_space hE) (smooth_test_values_hom hE) S ->
  exists T:(R_n R n->Y)->R,
    @is_distribution_continuous_extension R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y NY hNY (smooth_test_space hE) (smooth_test_values_hom hE) S T.
Proof.
move=>hFinite.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT:=real_norm_metric_space hN.
pose DT:=smooth_test_space hE.
pose values:=smooth_test_values_hom hE.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hOutside:forall phi:DT,forall x:XT,~U x ->values phi x=0.
  move=>phi x hx; exact:(@smooth_test_value_outside R X Y N NY hN hNY U E ev hE phi x hx).
have hAmbient:=@distribution_domain_finite_majorants R XT U Y NY hNY DT values hOutside S hFinite.
apply:(@distribution_continuous_extension_exists R XT U
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN)
  hOpen Y NY hNY DT values S hAmbient).
- move=>phi; exact:(@smooth_test_compact_continuous_field R X Y N NY hN hNY U E ev hE phi).
- move=>w hw; exact:(@compact_continuous_field_test_approximation R n Y NY hNY hY U hU E ev hE w hw.1 hw.2).
Qed.
