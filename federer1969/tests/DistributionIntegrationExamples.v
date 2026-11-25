(** Federer (1969), 4.1.5, pp. 349–350: boundary checks
    on the actual sealed test and distribution spaces.
    They include the zero distribution, a nonhomogeneous
    monotone bound, an empty open domain, and zero source
    and target dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  CompleteMetricUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  ContinuousRealDual ContinuousDualSealed WeakEvaluationTopologySealed OpenFamilyTopologyMathcomp
  FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses ExtendedSupremumUP
  DistributionVariationUP DistributionVariationSealed DistributionVariationBasic DistributionVariationDomain
  DistributionFiniteVariationUP NormalisedDistributionRepresentationUP FiniteDistributionRadonRepresentation
  DistributionMonotoneGaugeBounds DistributionMonotoneWeakCompactness DistributionsByIntegration.
From Federer Require Import
  AbstractDualCharacteristicPairing AbstractDualPairingDifference AbstractDualPartialPairing AbstractDualWeakEncoding AbstractUnitDualPairing
  BallIntegralQuotientLimitUP BallIntegralQuotientLocality BoundedContinuousDualCompact BoundedLinearProductCompact CharacteristicVectorLoneNorm
  CompactContinuousConvolutionApproximation CompactContinuousDomainAlgebra CompactContinuousDomainFields CompactContinuousFieldMultiplier CompactContinuousLoneDensity
  CompactContinuousOpenExtensionInverse CompactContinuousOpenExtensionLinear CompactContinuousSmoothingTests CompactContinuousSubspaceSupport CompactContinuousTestApproximation
  CompactContinuousTestLoneApproximation CompactContinuousVectorAlgebra CompactContinuousVectorFields CompactContinuousVectorMeasurable CompactContinuousVectorModule
  CompactContinuousVectorSpace CompactContinuousVectorZeroExtension CompactExhaustionInteriorCover CompactFieldUniformIntegralBound CompactFiniteMeasurePushforward
  CompactNormTailBookIdentity CompactNormTailExistence CompactNormTailFieldLaws CompactNormTailUP CompactScalarVectorIdentification
  CompactUniformApproximationAlgebra CompactUniformApproximationUP CompactUniformDaniellLimit CoveringBallIntegralQuotientLimit DaniellLinearTestRestriction
  DenseLoneExtensionUniqueness DenseWeakPositiveLimits DistributionCompactContinuousLimit DistributionCompactUniformLimits DistributionCompactUniformUniqueness
  DistributionContinuousExtensionExistence DistributionContinuousExtensionSealed DistributionContinuousExtensionUP DistributionExtensionApproximationBound DistributionExtensionSharpBound
  DistributionFiniteGaugeCutoff DistributionFiniteVariationUP DistributionIntegrationCriterion DistributionIntegrationRepresentationUP DistributionLoneExtension
  DistributionMonotoneGaugeBounds DistributionMonotoneWeakCompactness DistributionNormTailEstimate DistributionOriginalBallFormula DistributionOriginalRadonFormula
  DistributionRadonExtension DistributionRepresentationFiniteGauge DistributionSubspaceExtension DistributionSubspaceTestValues DistributionSubspaceVariation
  DistributionVariationBasic DistributionVariationBoundedExistence DistributionVariationCauchy DistributionVariationDomain DistributionVariationDomainFinite
  DistributionVariationExistence DistributionVariationFinite DistributionVariationLowerLimit DistributionVariationScaling DistributionVariationSealed
  DistributionVariationUP DistributionVariationUniformZero DistributionWeakLowerSemicontinuity DistributionsByIntegration DualLoneIntegralAlgebra
  DualLoneIntegralExistence DualLoneIntegralLipschitz DualLoneIntegralSealed DualLoneIntegralUP EuclideanDistributionContinuousExtension
  FiniteBoundedRealDifferentiation FiniteDistributionRadonRepresentation FiniteEuclideanDerivationContext FiniteEuclideanNormDerivationContext FiniteGaugeDistributionContinuity
  FiniteWeakDualBallQuotients FiniteWeakDualDifferentiation LoneCharacteristicBallQuotient LoneSeminormContinuityUP NormTailScalarLaws
  NormTailSmoothingBound NormalisedDistributionRepresentationUP NormalisedDistributionScalarIntegral NormalisedScalarIntegralGauge NormalisedWeakDensityCompactNorm
  OpenSubspaceLocalizedBallLimits OpenSubspaceWeakDualExtension OriginalGaugeRadonOpenLowerLimit PlateauSmoothingBound PositiveNormCauchy
  PositiveRealLinearLimits RadonCompactDualBallLimits RadonOpenSubspaceDualBallLimits RadonPositiveCompactOpenContent RealSubsetFiniteDifference
  RealValueSupremumScaling ScalarDaniellCompactExtension ScalarDaniellDistribution ScalarDaniellDistributionVariation ScalarDaniellRestrictionUP
  ScalarEvaluationMeanFamily SmoothClassOpenRestriction SmoothScalarTestCompactFunction SmoothTestCompactContinuous SmoothTestLoneDensity
  SmoothingUniformNormBound SubspaceLocalizedIntegral SubspaceSmallBallGeometry WeakDualDensityNormTransport WeakDualFunctionalNorm
  WeakDualRealisationContinuity WeakDualRealisationExistence WeakDualRealisationMeasurable WeakDualRealisationSealed WeakDualRealisationUP
  WeakDualScalarEvaluation WeakSequenceEvaluationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ActualOriginalSpaces.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Local Notation E := (@SmoothFunctionSpace.space R X Y N NY hN hNY U hU).
Local Notation ev := (@SmoothFunctionSpace.value R X Y N NY hN hNY U hU).
Local Notation hE := (@SmoothFunctionSpace.laws R X Y N NY hN hNY U hU).
Local Notation D := (@SmoothFunctionDerivatives.operators R X Y N NY hN hNY U E ev hE).
Local Notation hD := (@SmoothFunctionDerivatives.laws R X Y N NY hN hNY U E ev hE).
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation W := (open_family_topological_space (@continuous_real_dual_weak_laws R DT SO hSO).1).

(** Source for [actual_zero_distribution_gauge]: the zero
    boundary of the original supremum in Federer 4.1.5,
    p. 349, on every original positive compact test. *)
Theorem actual_zero_distribution_gauge (f:UT->R)
    (hf:positive_function_lattice (@compactly_supported_continuous_functions R UT) f):
  @DistributionVariation.value R UT Y NY hNY DT dvalues (eD (0:DD)) f hf.2=0%:E.
Proof.
have hGauge:=@DistributionVariation.laws R UT Y NY hNY DT dvalues (eD (0:DD)) f hf.2.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(@distribution_variation_least_finite_bound R UT Y NY DT dvalues (eD (0:DD)) f _ 0 hGauge).
  move=>phi hBound; by rewrite (linear0 eD) hom_zeroE.
- exact:(@distribution_variation_nonnegative R UT Y NY hNY DT dvalues (eD (0:DD)) f _ hf.2 hGauge).
Qed.

(** Source for [actual_nonhomogeneous_bound_compact]: the final
    theorem of Federer 4.1.5, p. 350, permits M(f)=1.
    In particular M(0) is nonzero: homogeneity was not
    silently added to its original monotonicity hypothesis. *)
Theorem actual_nonhomogeneous_bound_compact:
  compact [set T:W|@is_original_distribution_gauge_bounded R UT Y NY hNY DT dvalues
    (fun _=>1) (eD T)] /\ (1:R)!=0.
Proof.
split; last exact:oner_neq0.
apply:(@distribution_original_monotone_bound_weak_compact R n Y NY hNY U hU E ev hE D hD
  (fun _=>1)).
by move=>f g hf hg hFG.
Qed.

Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Local Notation YD := (@ContinuousDual.space R Y NY hNY).
Local Notation yd := (@ContinuousDual.evaluation R Y NY hNY).
Local Notation YN := (@ContinuousDual.norm R Y NY hNY).
Local Notation hYD := (@ContinuousDual.laws R Y NY hNY).
Local Notation YO := (@WeakEvaluationTopology.opens R Y YD (fun a y=>yd a y)).
Local Notation hYO := (@WeakEvaluationTopology.laws R Y YD (fun a y=>yd a y)).

(** Source for [actual_zero_distribution_radon_representation]:
    the original criterion and normalized representation,
    Federer 4.1.5, pp. 349–350, include the zero
    distribution on arbitrary open U. No nonzero-measure
    or nonzero-target premise is required. *)
Theorem actual_zero_distribution_radon_representation:
  exists rho:set UT->\bar R,exists k:UT->YD,
    is_normalised_distribution_representation hYD hYO dvalues (eD (0:DD)) rho k.
Proof.
apply:(@finite_distribution_radon_representation R n Y NY hNY hY hSep U hU E ev hE
  (eD (0:DD)) YD yd YN hYD YO hYO).
move=>f hf; exists 0.
have hGauge:=@DistributionVariation.laws R UT Y NY hNY DT dvalues (eD (0:DD)) f hf.2.
by rewrite (actual_zero_distribution_gauge hf) in hGauge.
Qed.
End ActualOriginalSpaces.

Section ActualEmptyZeroDimensions.
Variable R:realType.
Local Notation X := (R_n R 0).
Local Notation N := (inner_norm (@euclidean_inner_productP R 0)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 0)).
Local Notation hEmpty := (fun x (hx:False)=>False_rect (norm_domain_interior N set0 x) hx).
Local Notation E := (@SmoothFunctionSpace.space R X X N N hN hN set0 hEmpty).
Local Notation ev := (@SmoothFunctionSpace.value R X X N N hN hN set0 hEmpty).
Local Notation hE := (@SmoothFunctionSpace.laws R X X N N hN hN set0 hEmpty).
Local Notation D := (@SmoothFunctionDerivatives.operators R X X N N hN hN set0 E ev hE).
Local Notation hD := (@SmoothFunctionDerivatives.laws R X X N N hN hN set0 E ev hE).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation W := (open_family_topological_space (@continuous_real_dual_weak_laws R DT SO hSO).1).
Local Notation UT := (set_type (set0:set (real_norm_metric_space hN))).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hN) set0 X DT (smooth_test_values_hom hE)).

(** Source for [actual_empty_zero_dimensions_compact]: the
    empty-domain boundary of the final theorem in Federer
    4.1.5, p. 350, on actual sealed R^0-valued
    tests on the empty open subset of R^0. *)
Theorem actual_empty_zero_dimensions_compact:
  compact [set T:W|@is_original_distribution_gauge_bounded R UT X N hN DT dvalues
    (fun _=>1) (eD T)].
Proof.
exact:(@actual_nonhomogeneous_bound_compact R 0 X N hN set0 hEmpty).1.
Qed.
End ActualEmptyZeroDimensions.
