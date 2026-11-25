(** Federer (1969), 4.1.4, pp. 348–349: a distribution
    whose coordinate derivatives vanish on connected open A
    is integration against a single continuous linear
    functional on tests supported in A. The original test
    domain and literal scalar integral over U are preserved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestEvaluation SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP ContinuousTestSmoothingConvergence
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothGlobalTranslationSealed NormDifferentialUP NormOpenDomainLaws
  EuclideanLebesgueDimensions ContinuousDualUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothedKernelDensityFamily
  ContinuousDistributionIntegralAction DistributionIntegralFieldUP
  DistributionDirectionalDerivative NormRegularity ContinuousRealFunctional ContinuousDualSealed SmoothingKernelSealed SmoothingDilationSealed
  ContinuousSmoothSmoothingExistence TestSmoothingFamilyExistence SmoothedDistributionInnerConstancy
  InnerParallelFamilySealed InnerComponentFamilySealed RegularisationConstantRepresentation
  SmoothedKernelIntegralFamily ContinuousDistributionTestLimit PositiveNormLimitUP SummableRealFunctionUP MeasureIntegralUP
  GlobalDistributionConstancy SmoothCompactCutoffSealed SmoothCompactCutoffUP NormRegularityOperations
  CompactSupportFunctionUP CompactTestDistributionExtension CompactTestExtensionLocality TestZeroExtensionSealed
  TestZeroExtensionLaws TestZeroExtensionUP SmoothTestEvaluation LinearBasis
  CompactDomainDistributionConstancy DomainConstantFunctionalUniqueness SmoothCompactExhaustionSealed
  CompactExhaustionConnectedNeighbourhood NormBoundedLinearTopology OpenDomainDistributionConstancy
  ContinuousRealDual FunctionalSupportUP DistributionDerivativeLocality TestScalarSubsetIntegral
  MeasureSubsetIntegral MeasureIntegralGraphEquivalence LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionConstancy.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y N hN U DT (smooth_test_value hE)).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).



Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation tsupport := (@smooth_functional_support R X Y N hN U DT (smooth_test_value hE)).
Variable T:DD.
Variable A:set X.
Hypothesis hOpen:@open (real_norm_metric_space hN) A.
Hypothesis hConnected:@connected (real_norm_metric_space hN) A.
Hypothesis hAU:A `<=` U.
Hypothesis hDerivativeSupport:forall i:'I_n,forall x,
  tsupport (eD (@distribution_directional_derivative R X Y N NY hN hNY U hU E ev hE D hD
    (@coordinate_basis R n i) T)) x ->U x /\ ~A x.

(** Source for [distribution_derivative_support_constant]: the
    original theorem of Federer 4.1.4, pp. 348–349. If A is
    connected and open in U and spt D_j T lies in U minus A
    for every coordinate, there is a continuous linear alpha
    on Y with T(f)=integral_U alpha(f) for every original
    test f on U supported in A. Empty A, n=0 and arbitrary
    Banach targets are retained. The p. 348 line 26 erratum
    specifies the original test space D(U,Y). *)
Theorem distribution_derivative_support_constant:
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,support f `<=` A ->
      is_measure_subset_integral (@euclidean_lebesgue_measure R n) U
        (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (eD T f)%:E.
Proof.
have hT:=@continuous_real_dual_member_continuous R DT SO hSO T.
have hAnn:forall i:'I_n,forall f:DT,support f `<=` A ->
    eD T (@distribution_test_directional_derivative R X Y N NY hN hNY U hU E ev hE D hD
      (@coordinate_basis R n i) f)=0.
  move=>i f hSupp.
  exact:(@distribution_derivative_support_annihilation R X Y N NY hN hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE D hD T
    (@coordinate_basis R n i) A (@hDerivativeSupport i) f hSupp).
case:(pselect (exists a:X,A a))=>[[a ha]|hEmpty].
- have[alpha [hAlpha hRep]]:=@open_domain_distribution_annihilating_derivatives_constant R n Y NY hNY hY
    E ev U hU hE D hD (eD T) hT A hOpen hConnected hAU a ha hAnn.
  exists alpha; split=>// f hSupp.
  exact:(@smooth_test_scalar_subset_integral R X Y N NY hN hNY U E ev hE
    (@euclidean_lebesgue_measure R n) alpha f (eD T f)%:E (@hRep f hSupp)).
- exists (0:Hom Y R^o); split.
  + apply:(@bounded_real_functional_continuous R Y NY hNY (hom_as_linear (0:Hom Y R^o)) 0 (lexx _)).
    move=>y; by rewrite hom_as_linearE hom_zeroE normr0 mul0r.
  + move=>f hSupp.
    have hSupportEmpty:support f `<=` set0.
      move=>x hx; apply:hEmpty; exists x; exact:(hSupp x hx).
    have hZero:=@smooth_test_empty_support_zero R X Y N NY hN hNY U E ev hE f hSupportEmpty.
    apply:(@smooth_test_scalar_subset_integral R X Y N NY hN hNY U E ev hE
      (@euclidean_lebesgue_measure R n) (0:Hom Y R^o) f (eD T f)%:E).
    rewrite hZero linear0.
    have hIntegral:=@real_total_zero_integral R X (@euclidean_lebesgue_measure R n)
      (euclidean_lebesgue_is_measure R n).
    apply:(measure_integral_graph_equivalent _ hIntegral)=>x z.
    by rewrite !real_total_integrand_graph.
Qed.
End DistributionConstancy.
