(** Federer (1969), 4.1.5, pp. 349–350:
    the representing weak dual density gives the
    literal integral formula for every original
    test. Exact extension agreement changes T(phi)
    back to the original S(phi). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  CompactContinuousVectorFields VectorDaniellHypotheses VectorDaniellRepresentationUP
  SummableRealFunctionUP MeasureIntegralUP DistributionContinuousExtensionUP
  DistributionSubspaceExtension DistributionSubspaceTestValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_original_radon_formula]:
    S(phi)=integral <phi,k> d||S|| for every
    original phi in D(U,Y), Federer 4.1.5,
    p. 350. The actual subset U and original
    test values are retained. *)
Theorem distribution_original_radon_formula (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (S:Hom (smooth_test_space hE) R^o)
    (T:(X->Y)->R)
    (mu:set (set_type (U:set (real_norm_metric_space hNX)))->\bar R)
    (k:set_type (U:set (real_norm_metric_space hNX))->weak_dual_space hNY):
  @is_distribution_continuous_extension R (real_norm_metric_space hNX) U Y NY hNY
    (smooth_test_space hE) (smooth_test_values_hom hE) S T ->
  is_vector_daniell_density mu
    (@compact_continuous_vector_fields R (set_type (U:set (real_norm_metric_space hNX))) Y NY hNY)
    (@distribution_subspace_extension R (real_norm_metric_space hNX) U Y T) k ->
  forall phi:smooth_test_space hE,is_measure_integral mu
    (real_total_integrand (fun x=>val (k x) (smooth_test_value hE phi (set_val x)))) (S phi)%:E.
Proof.
move=>hT hDensity phi.
pose w:=fun x:set_type (U:set (real_norm_metric_space hNX))=>smooth_test_value hE phi (set_val x).
have hMember:=@smooth_test_original_continuous_field R X Y NX NY hNX hNY U E ev hE phi.
have hI:=vector_daniell_density_integral hDensity hMember.
by rewrite (@distribution_subspace_test_value R X Y NX NY hNX hNY U E ev hE S T hT phi) in hI.
Qed.
