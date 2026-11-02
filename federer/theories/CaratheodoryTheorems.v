(** Public exports for Federer (1969), subsection 2.10,
    pp. 169–206. This export introduces no mathematical
    declaration. Source passages and edition comparisons
    accompany each exported declaration. The constructions
    of the metric and corrected topological measures, refined
    envelopes and two-point witness remain behind opaque
    interfaces. Coverage includes item 2.10.1 and the integer-degree
    development of 2.10.2 and items 2.10.3–2.10.4, with the checked core of 2.10.5; the optional real-degree Gamma
    extension and the printed circle example remain pending. This
    export does not claim completion of all of subsection 2.10. *)
From Federer Require Export
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleEnvelope MetricScaleSeparation
  MetricScaleBorelHull CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryMetricMeasure
  CaratheodoryBorelRegular CaratheodoryMeasure
  CaratheodoryScaleConvergence CaratheodorySingleGenerator CaratheodoryApproximationCounterexamples
  MetricOpenCoverLayers OpenRefinementBoundUP MetricScaleApproximation
  MetricRefinementApproximation MetricRefinementCharacterization
  TwoPointOpenTopologyUP TwoPointOpenTopologySealed OpenRefinementNonmonotonicity
  OpenRefiningEnvelopeUP OpenRefiningEnvelopeLaws OpenRefiningCoverCost
  OpenRefiningEnvelopeSealed OpenRefiningEnvelope
  TopologicalCaratheodoryUP TopologicalCaratheodoryLaws TopologicalCaratheodoryMeasure
  TopologicalCaratheodorySealed TopologicalOpenRefinementBound
  CommonOpenCover OpenRefiningSeparation ContinuousMetricBallCover
  TopologicalContinuousMeasurability TopologicalCaratheodory TopologicalMetricAgreement.
From Federer Require Export
  CaratheodoryFamilyReplacement ConvexHullSealed ConvexHull EuclideanBallDiameter
  MetricBallDiameterUP EuclideanBallDiameterFactor HausdorffDiameterCost HausdorffMeasureUP
  HausdorffMeasureLaws HausdorffMeasureSealed HausdorffMeasure HausdorffClosedCoverAgreement
  NormConvexHullDiameter HausdorffConvexCovers UnitAtomCountingMeasure HausdorffCountingMeasure
  HausdorffPowerCostLaws HausdorffDimensionGauge MetricScaleMeasureBound MetricScaleWeightedBound
  HausdorffDimensionDrop HausdorffGaugeContinuity HausdorffSphericalComparison HausdorffCountableNull
  HausdorffLengthCompatibility MetricOpenThickening HausdorffOpenCoverAgreement HausdorffOpenCutoffCounterexample
  SphericalOpenBallUP OpenBallScaleBound SphericalCountingMeasure SphericalOpenBallAgreement.
From Federer Require Export
  AffineConvexPreimage MetricCoordinateBoxes CompactCoordinateNeighbourhood EuclideanBoundedClosure
  EuclideanConvexDiameter ExteriorDiameterUP ExteriorDiameterLaws
  ExteriorDiameterSealed ExteriorDiameter ExteriorMeasureGauge ExteriorMeasureUP
  ExteriorMeasure ExteriorCompactCoverUP SeparateAffineHullBound ExteriorCoordinateLinearity
  ExteriorEndpointAffinity ExteriorEndpointContinuity FiniteCoordinateClosure ExteriorDiameterClosure
  ExteriorCompactCoverAgreement ExteriorDiameterConvexity ExteriorConvexCoverAgreement ExteriorDegenerateGauges
  ExteriorDiameterBound ExteriorOpenCoverUP ExteriorOpenEnlargement ExteriorOpenCoverAgreement.
From Federer Require Export
  OpenConvexContractions AffineDilation InnerConvexNeighbourhoods ProjectedVolumeGaugeUP
  ProjectedVolumeGauge EuclideanScalarLength LineProjectionAttainment ScalarConvexLength
  ProjectedVolumeDegreeOne ProjectionMeasureUP ProjectionMeasure ProjectedVolumeDilation
  RealDilationSlack ProjectedVolumeClosure EuclideanProjectionSpace EuclideanCompactOpenVolume
  MetricCompactNeighbourhood CompactProductTube ProjectedVolumeOpenEnlargement EuclideanClosedDiameterCompact
  ProjectionClosedOpenComparison CaratheodoryProjectionLength.

(** Core definitions and continuity laws of 2.10.5, pp. 172–173.
    The consequences and all-exponent open/closed convex comparison
    are exported below, completing the printed item. *)
From Federer Require Export
  BoundedProbabilityExponentNorm CompactCauchyLimits CountableBaseDenseSet
  EuclideanProjectionMetric MeasurableNonnegativeExtendedPower
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNormSealed
  NonnegativeExtendedExponentNorm OrthogonalProjectionProbabilityUP
  OrthogonalProjectionProbabilitySealed EuclideanMetricCompleteness
  EuclideanMetricSeparability ProjectedVolumeIncidence ProjectedVolumeMeasurability
  OrthogonalProjectionProbability ProjectionBetaSealed ProjectionBeta IntegralGeometricGauge
  NonnegativeExtendedScalarNorm ProjectedVolumeBounds BoundedProjectedVolumeNorm
  CompactProjectedVolumeUpperContinuity EuclideanLebesgueCompactInner
  ProjectionBetaContinuity IntegralGeometricGaugeContinuity IntegralGeometricMeasureUP
  IntegralGeometricMeasure NonnegativeExtendedEssentialBounds ProjectionImageLifting
  OpenProjectionIncidence ProjectedVolumeLowerContinuity ProjectionProbabilitySupport
  IntegralGeometricInfinity ProjectedVolumePointwiseClosure
  ProjectedVolumeParameterContinuity.

(** Further 2.10.5 consequences, pp. 172–173: arbitrary-target
    normalized-measure monotonicity, the Borel projection-null
    characterization and common null sets. The finite-exponent
    open/closed convex construction equality is followed by the
    infinity endpoint and the full all-exponent theorem below. *)
From Federer Require Export
  NonnegativeExtendedNormAlmostEquality NonnegativeExtendedNormFiniteValues CaratheodoryWeightedComparison
  ProbabilityNonnegativeExtendedNorm IntegralGeometricExponentMonotone NonnegativeExtendedNormZero
  ProjectionIncidenceMeasure IntegralGeometricNullCover IntegralGeometricNullSets
  IntegralGeometricClosure.

(** Finite-exponent closed convex comparison for 2.10.5(2),
    p. 173, via compact-source thickenings and the dominated
    convergence theorem. The infinity endpoint is exported next. *)
From Federer Require Export
  CompactProjectedVolumeThickening BoundedExtendedNormConvergence
  ProjectedThickeningBounds IntegralGeometricFiniteEnlargement
  IntegralGeometricFiniteClosedCovers.

(** Completion of 2.10.5(2), p. 173, including the infinity
    endpoint. Positive projected volume supplies a simplex section
    buffer. Nearby projections admit bounded correcting inverses,
    proving compact-convex lower volume continuity and the actual
    infinity-gauge identity. Finite-cutoff covering comparison then
    gives full open/closed convex construction equality. *)
From Federer Require Export
  FiniteSubsetSpan PositiveVolumeAffineSpan ConvexSimplexBuffer
  ConvexProjectionSectionBuffer PositiveProjectedVolumeBuffer NearIdentityEuclideanInverse
  RectangularEuclideanContinuity CompactProjectionEvaluationControl NearbyProjectionSections
  ConvexSectionContraction ConvexProjectedContraction CompactConvexProjectedVolumeLower
  CompactConvexInfinityGauge IntegralGeometricClosedCovers.

(** Federer 2.10.7, pp. 174–175: the original raw-increment
    interval construction, all positive-cutoff identities, actual
    induced-measure identification, and real-line H1=Lebesgue.
    Source comments accompany the exported declarations. *)
From Federer Require Export
  StieltjesCaratheodoryUP StieltjesIntervalBounds StieltjesCaratheodory
  MonotoneIntervalSubdivision StieltjesScalePointNull StieltjesScaleSubdivision
  RealHausdorffLebesgue StieltjesInducedOpenIntervals StieltjesIntervalUniqueness
  StieltjesCaratheodoryConsequences StieltjesCaratheodoryIdentification.

(** Federer 2.10.8, p. 175: all Borel partition costs,
    shrinking partitions without refinement, and the equivalence
    with the printed countable-family hypothesis. Named declarations
    carry their own source locators. *)
From Federer Require Export
  BorelCoverCostUP BorelCoverCostFamilies BorelPartition BorelCaratheodoryMeasure
  BorelPartitionCoverBounds SmallBorelPartitionFamilies BorelPartitionCharacterization
  BorelPartitionCostConvergence BorelPartitionTheorem.

(** Federer 2.10.9, p. 175: partition formulas for Gross
    and integral-geometric measures, actual countable-cover
    cost laws, the full left-exponent limit on arbitrary targets,
    and the multiplicity definition. Source comments accompany
    every mathematical declaration. *)
From Federer Require Export
  GrossBorelPartitions ProbabilityScalarNormLeftContinuity ProbabilityExtendedNormLeftContinuity
  IntegralGeometricGaugeLeftContinuity NonnegativeExtendedNormOrder ProbabilityScalarLpMembership
  ScalarLpFiniteSums ScalarLpCountablePositiveBound ProbabilityExtendedNormCover
  IntegralGeometricCoverCosts IntegralGeometricBorelPartitions CountableCommonBorelHulls
  BorelCaratheodoryScale BorelCaratheodoryIncreasingCosts IntegralGeometricNormalizedLimit
  PositiveNormalizationLimit RealIncreasingLowerApproximation ProjectionBetaSequenceLimit
  IntegralGeometricExponentLimit HausdorffCostCoverCounterexample MappingMultiplicity.

(** Integer-degree Hausdorff core of Federer 2.10.11, p. 176.
    The optional real-degree extension and the spherical variant
    remain pending; this export does not claim the entire item. *)
From Federer Require Export
  LipschitzCaratheodoryTransport HausdorffLipschitzCost HausdorffLipschitzImages
  BorelCaratheodoryMeasureBound LipschitzMultiplicityInteger.

(** Federer 2.10.12, p. 176: connected sets have H1 at
    least their diameter, on arbitrary metric spaces. Source
    comments and the expanded distance-map argument are in
    ConnectedHausdorffLength.v. *)
From Federer Require Export ConnectedHausdorffLength.

(** Federer 2.10.13, p. 177: continuous curve length, the actual
    multiplicity integral, and the null-image criterion for absolute
    continuity. The metric strengthening and source locators accompany
    the declarations in the exported modules. *)
From Federer Require Export
  MetricCurveLocalization HausdorffLengthRestrictedMaps CurveImageLengthBound
  BorelImageMeasureBounds CurveImageMeasureLower CurveImageMeasureUpper
  CurveLengthMultiplicity MetricAbsoluteContinuityFiniteVariation ArcLengthImageMeasure
  ImageNullAbsoluteContinuity CurveNullImageCriterion ContinuousCurveLength.

(** Federer 2.10.14, p. 177: the corrected upper-integral
    curve formula with both oriented jump sums. The construction
    of the auxiliary weighted measure remains behind its seal. *)
From Federer Require Export
  CurveOneSidedJumpUP CurveOneSidedJumpContinuity WeightedCountingMeasureUP
  WeightedCountingMeasureSealed WeightedCountingMeasure
  CurveJumpArcLength CurveFirstLevelCrossing CurveCrossingJumpBounds
  CurveJumpBridgeCover CountablyDiscontinuousImages CurveEndpointJumpEstimate
  CurveJumpLocalization CurveArcLengthAtoms CurveJumpBudget
  CurveJumpEndpointBound DiscontinuousCurveMeasureBound CurveDiffuseAtomicBound
  RetractedCurveJumpBudget CurveJumpVariationLower CurveJumpVariationUpper
  CurveUpperMultiplicity DiscontinuousCurveLength CurveIsolatedJump.

(** Federer 2.10.15, p. 178: projection-multiplicity norm
    bounds and the exponent-one iterated-integral formula.
    The declarations retain the actual theta-star and beta. *)
From Federer Require Export
  NonnegativeExtendedNormLimitBound ProjectionMultiplicityIntegral
  TotalIncreasingIntegralValues PositiveFiniteSupremumScale
  ProjectionMultiplicityPartitions IntegralGeometricMultiplicity.

(** Federer 2.10.16, p. 178: joint counting measurability
    and all three affine/projection slicing identities.
    Source passages and the double-normal averaging proof
    are annotated in the exported declarations. *)
From Federer Require Export
  BijectionPostcompositionMultiplicity ContinuousFamilyIncidence CountableBorelProduct
  EuclideanBlockLinear EuclideanNormalJacobian EuclideanProjectionComposition
  HaarProbabilityTranslations MeasureBijectionTotalIntegral OrthogonalProbabilityBackground
  PartitionComposedMultiplicity ProductMeasureShuffle ProjectionJointMultiplicity
  ProjectionNormalVector SuslinImageCostHull SuslinPartitionCostLimits
  SuslinProjectionCostHull TotalNonnegativeExtendedScaleIntegral TotalNonnegativeProductIntegral
  TotalSandwichIntegralSupremum AffineSliceCount ContinuousFamilyMultiplicity
  LinearPostcompositionMultiplicity ProjectionCompositionProbability ProjectionJointMultiplicityIntegral
  ProjectionMultiplicityPrecomposition ProjectionNormalJacobian ProjectionNormalOrbit
  ProjectionPartitionPrecomposition ProjectionProductRegularity RotatedProductIntegral
  StackedNormalFamily SuslinIntegralGeometricPartitions SuslinMultiplicityIntegral
  SuslinProjectionJointMultiplicity AffineParameterMultiplicity ContinuousFamilyPrecomposition
  ProjectionMultiplicityParameterisation StackedNormalAdjoint StackedNormalSliceParameters
  SuslinProjectionMultiplicity ProjectionCompositionAverages ProjectionOrbitMultiplicity
  StackedNormalCounting StackedNormalJacobian SuslinProjectionPartitions
  LinearOrbitMultiplicityIntegral StackedNormalJacobianAverage StackedNormalOrbitJacobian
  SuslinIntegralGeometricMultiplicity AffineGeometricSlice StackedNormalPairIntegral
  SuslinProjectionJointIntegral ProjectionComposedCountIntegral StackedNormalAverageCount
  AffineParameterGeometricIntegral IntegralGeometricProjectionSlice IntegralGeometricAffineSlicing
  IntegralGeometricProjectionSlicing.

(** Federer 2.10.17, p. 179: density estimates and the necessary nonnegative
    zero-denominator correction. The exported declarations distinguish the
    original partial quotient, its counterexample and the corrected density
    convention. *)
From Federer Require Export
  CaratheodoryDensityQuotient CaratheodoryDensityScaleBound CoveringConstantLimit
  FiniteMeasureSelfContraction MetricScaleLocalAgreement SubsingletonCoverCost
  CaratheodoryDensityFunction CaratheodoryDensityGoodSets SubsingletonCoverMeasure
  SubsingletonPointRatio CaratheodoryDensityGoodNull CaratheodoryDensityLocalBound
  SubsingletonDensityCorrection SubsingletonDensityCounterexample CaratheodoryDensityUpperBound
  CaratheodoryDensityLowerBound CaratheodoryDensityScaleTheorem.

(** Federer 2.10.18, pp. 180–181: controlled enlargement,
    the open-set lower estimate, the full zero-density
    limit off a finite measurable set, and the upper
    density at most one for a finite arbitrary set.
    The source-annotated declarations retain the original
    partial quotient under the printed strict cost growth. *)
From Federer Require Export
  ExtendedScaledErrorBound FiniteRemainderMeasureComparison DiameterEnlargements
  CaratheodoryEnlargementUP CaratheodoryEnlargementGrowth CaratheodoryDensityLargeCells
  CaratheodoryEnlargementSelection CaratheodoryEnlargementScaleBound CaratheodoryEnlargementDensityBound
  CaratheodoryPositiveCostLimits CaratheodoryOffSetDensity CaratheodoryZeroDensityLimit
  FiniteBorelOpenInfimum CaratheodoryFiniteDensityBound FiniteMeasureSelfExpansion
  CaratheodorySubmeasureDensity CaratheodoryRestrictedDensity.

(** Federer 2.10.19, p. 181: integer-degree metric densities and all five
    consequences. The optional real-degree Gamma normalization remains with
    2.10.2. its witness remains behind the sealed interface and all source
    locators accompany declarations. *)
From Federer Require Export
  CaratheodoryWeakEnlargementUP DensityDenominatorComparison HausdorffAllSets
  HausdorffSubcriticalMetricDensity HausdorffUpperMetricDensity MetricDensities
  MetricDensityHausdorffGauge MetricDensityNumericalBounds MetricDensitySmallBalls
  PolynomialRadiusUpperBound PositiveRadiusLimitBounds PositiveRadiusLimitCongruence
  PositiveRadiusLimits SphericalBallCostBound SphericalEnlargement
  SphericalEnlargementUP SphericalMetricDensityComparison SphericalMetricDensityTheorems
  WeakCaratheodoryDensityLargeCells WeakCaratheodoryDensityQuotient WeakCaratheodoryEnlargementDensityBound
  WeakCaratheodoryEnlargementScaleBound WeakCaratheodoryEnlargementSelection WeakCaratheodoryFiniteDensityBound
  WeakCaratheodoryOffSetDensity WeakCaratheodoryOffSetUpperDensity WeakCaratheodoryRestrictedDensity
  WeakCaratheodorySubmeasureDensity.

(** Federer 2.10.20, pp. 181–182: fixed-scale and
    final-measure radial exhaustion, open-generator compact
    continuity and the interior-refinement compact inequality.
    All four claims retain infinite values; source comments
    explain the shell and open-envelope proof expansions. *)
From Federer Require Export
  CompactDecreasingNeighborhoods CompactOpenEnvelopeBound CompactScaleContinuity
  InteriorRefiningMetricCost MeasurableBallRadialContinuity RadialMassSupremum
  RadialScaleContinuity RadialShellMeasureBounds RadialShells.

(** Federer 2.10.21, pp. 182–184: closed Lipschitz
    families, compact-uniform convergence, the sealed Hausdorff
    metric, compact bounded hyperspaces, finite approximations,
    diameter bounds and compact convex hulls. Precise source
    comments accompany the declarations; the convex density scope
    follows the erratum p. 3, book p. 184 lines 8 and 10. *)
From Federer Require Export
  CompactBallProfiles CompactBallProfilesClosed CompactBallProfilesCompact
  CompactConvexProfiles CompactHausdorffBall CompactHausdorffMetric
  CompactMetricBounded CompactProfileNearest CompactProfileSublevels
  CompactSetDistanceProfile ConvexProfileClosed FiniteNormBoundedCompact
  FiniteNormCompactHull HausdorffConvexHulls HausdorffDiameter
  HausdorffDistance HausdorffDistanceBasic HausdorffDistanceUP
  HausdorffFiniteConvexHulls HausdorffFiniteNets HausdorffProfileContinuity
  LipschitzCompactConvergence LipschitzFunctionClosed LipschitzFunctionCompact
  LipschitzProductConvergence NormSubconvexCompact RealLineBoundedCompact.

(** Federer 2.10.22, pp. 184–186: finite positive
    cutoff approximations are continuous below for arbitrary
    increasing sets in a boundedly compact metric space.
    Compact costs retain exactly their continuity and positivity
    hypotheses. The positive-cost enumeration witness is sealed;
    precise source comments explain finite-cover flags, null
    exceptions and the finite-prefix compact-limit proof. *)
From Federer Require Export
  CompactArrayCluster ArrayClusterCost ArrayClusterClosed
  CompactGeneratorCostUP CompactGeneratorCostLaws SummableCostEnumerationUP
  CompactCostArray CompactZeroCostGenerators MetricScaleOptionalCover
  FiniteRealMaximum SummablePositiveMaximum SummableCostEnumeration
  SummableCostEnumerationLaws CompactCostCoverRow CompactCostSourceArray
  HausdorffCompactNeighborhood MaskedCompactGenerators CompactCostLimitArray
  MetricScaleMaskedCover CompactCostOpenResidual CompactOuterApproximation
  CompactCostTailRefinement MetricClosedRemovalBound CompactCostMixedResidual
  CompactCostLimitCoverBound CompactCostBoundedContinuity CompactCostContinuityBelow
  CompactCostScaleFinite.

(** Federer 2.10.23, p. 186: compact inner
    approximation of every Suslin set for the final
    measure. The pruning witness is sealed; continuity
    below replaces cutoff-measure regularity, and continuous
    compact refinements supply the required two-cutoff
    compact inequality without assuming monotone costs. *)
From Federer Require Export
  CompactCostOpenEnvelope IncreasingProjectionLoss ContinuousPruning
  CompactCostSuslinApproximation CompactCostSuslinBounds CompactCostSuslinInner.

(** Federer 2.10.24, pp. 186–188: finite-real weighted
    covering infima and their actual positive-cutoff limit;
    general upper-integral comparison, sigma-finite-support
    equality and the compact-continuous-cost equality criterion.
    Existence witnesses are sealed. Precise source comments
    distinguish supporting steps and the weak-cost extension. *)
From Federer Require Export
  BorelFiniteIncreasingCover BorelHullGeneratorBounds CaratheodoryNullGenerators FiniteDisjointWeightedLayers
  FiniteEnlargedCoverCost FiniteEnlargedDisjointCover SummableExceptionalSets WeightedCoverCutoffs
  WeightedMetricEnvelopeUP WeightedRepeatedGenerators BorelUniformGeneratorBounds FiniteWeightedGeneratorSums
  IncreasingBorelApproximation WeightedCoverReindexing WeightedCoverScale WeightedGeneratorIntegral
  WeightedMetricEnvelopeLaws WeightedMetricLimitUP CaratheodoryUniformBorelApproximation CountableWeightedLevels
  FineWeightedCoverAssembly FiniteWeightedEnlargementBound WeightedBorelFatouBound CountableWeightedEnlargementBound
  WeightedLevelCoverBound WeightedMetricEnvelope FiniteStepWeightedLevels WeightedLimitLevelBound
  WeightedMetricLimitLaws WeightedMetricLimit WeightedUpperIntegralBound WeightedSigmaFiniteEquality
  WeightedContinuousScaleEquality WeightedStrictEnlargementEquality WeightedCompactCostEquality.

(** Local correction to Federer 2.10.24, p. 188:
    actual closed balls in a compact real subspace
    approach a non-ball in the sealed Hausdorff metric.
    This refutes the auxiliary closed-family assertion;
    it does not refute the spherical integral equality. *)
From Federer Require Export ClosedBallHausdorffCounterexample ClosedBallHausdorffApproximation.

(** Federer 2.10.24, pp. 187–188: Hausdorff and spherical
    equalities under sigma-finite positive support, and their
    unconditional boundedly compact applications. Original
    generator families are preserved; Hausdorff comparison
    repairs the printed spherical closed-family argument. *)
From Federer Require Export
  ClosedHausdorffEnlargementUP HausdorffCompactCost HausdorffCompactScaleAgreement SphericalWeightedSigmaFinite
  UpperIntegralSupportCover WeightedCoverInjectiveTransport WeightedMeasurableHullBounds ClosedHausdorffEnlargement
  HausdorffGeneratorEnlargement HausdorffWeightedSigmaFinite HausdorffProperWeighted SphericalProperWeighted.

(** Federer 2.10.24, p. 188, final paragraph:
    weighted projection and integral-geometric cost estimates.
    These supporting inequalities do not yet assert the
    final integral equalities for these constructions. *)
From Federer Require Export WeightedImageThresholdBound ProjectedVolumeWeightedCovers
  NonnegativeExtendedNormScale IntegralGeometricWeightedCovers.

(** Supporting final-paragraph infrastructure for Federer 2.10.24,
    p. 188: limiting countable subadditivity, almost-order and
    homogeneity, an independently specified and sealed restricted
    measure, metric Borel measurability and the Borel indicator
    lower bound from 2.10.8. Construction witnesses remain private;
    the complete integral applications follow in the next group. *)
From Federer Require Export WeightedCountableSubadditivity WeightedFunctionOrderAndScale
  WeightedRestrictionMeasureUP WeightedRestrictionMeasureLaws WeightedRestrictionMeasure
  WeightedRestrictionSeparation WeightedBorelCoverCostUP WeightedBorelIndicatorBounds ProjectedWeightedBorelCosts.

(** Federer 2.10.24, p. 188, final paragraph: the full
    Gross and integral-geometric weighted-integral equalities
    for arbitrary nonnegative extended inputs. Borel majorants,
    arbitrary-target indicators and lower-step comparisons expand
    the reference to 2.10.8. All objects retain their abstract
    specifications and existing opaque implementation boundaries. *)
From Federer Require Export WeightedBorelLevels WeightedMeasurableMajorant WeightedIndicatorOrdinaryBound
  WeightedBorelIndicatorHulls BorelNullTransfer WeightedRestrictionBounds WeightedLowerStepBound
  WeightedBorelIntegralEquality ProjectedWeightedIntegralEquality.

(** Fibre upper-integral estimate 2.10.25, pp. 188–189,
    with natural degrees and the printed alternative
    support/properness condition. Source comments accompany
    the component declarations; this block only exports. *)
From Federer Require Export
  IncreasingUpperIntegralBound WeightedGeneratorImageAssembly HausdorffFibreCost HausdorffFibreWeightedBound HausdorffNullImageFibres HausdorffFibreCutoffs HausdorffFibreIntegralBound HausdorffFibreTheorem.

(** Fibre measurability and the nonmeasurable inclusion
    example of 2.10.26, pp. 189–190, in the
    natural-degree interfaces. Source comments accompany
    the declarations; this block only exports them. *)
From Federer Require Export
  CompactFibreOpenCovers CompactHausdorffOpenApproximation CompactFibreMassLevels CompactFibreMeasurability ZeroUpperIntegral SubsetInclusionFibreCounterexample CompactMetricSubset HausdorffMetricSubset NullFibresCompactImage NullFibresProperSource ProperMetricCompactApproximation CompactUnionFibreMeasurability HausdorffFibreMeasurability.

(** Product and section inequalities of 2.10.27,
    pp. 190–191, in the natural-degree interfaces.
    Source comments accompany the declarations;
    the auxiliary profile construction stays private. *)
From Federer Require Export
  MetricCartesianProductUP ImageFibreWeightedBound HausdorffFamilyCutoffs NonexpandingFibreImages HausdorffProductSections HausdorffProductLowerBound EuclideanMetricProduct HausdorffRadiusCost EuclideanClosedBallVolume EuclideanBallSections SphericalScaleBallBound EuclideanBallSectionProfileUP EuclideanBallSectionProfile SphericalEuclideanSections SphericalFamilyCutoffs EuclideanSphericalCutoff EuclideanSphericalSections.

(** Special interval families, their four properties, and
    power-gauge Cantor distributions of 2.10.28, pp. 191–193.
    The corrected root hypothesis follows the erratum, p. 4.
    Source comments accompany every declaration; existence
    constructions and sealing implementations remain private. *)
From Federer Require Export
  CompactIntervalCoverMargin ConcaveIntervalGaugeUP FiniteCumulativeFunctionUP FiniteIntervalBoundaryUP FiniteOptionalSum FiniteOrdinalSpan FractionalPowerConcavity IntervalClipLength ConcaveIntervalGaugeLaws FiniteCumulativeFunctionLaws FiniteIntervalBoundaries FiniteIntervalClippingPointwise PowerConcaveIntervalGauge CantorSplitRadiusUP CompactIntervalGauge ConcaveIntervalClipping EqualSpacingClippedCount EqualSpacingConcaveSpan RestrictedCumulativeLocality RestrictedCumulativeRange CompactIntervalDiameter CompactIntervalGaugeGeometry ConcaveIntervalMeasure ConcaveIntervalOpenEnlargement FiniteCumulativeFunction FiniteIntervalClippingSum SpecialIntervalFamilyUP ConcaveIntervalDistributionBounds ConcaveIntervalFiniteOpenCover EqualSpacingIntervalGeometry FiniteIntervalClippingBound PowerIntervalLengthBound SpecialIntervalFamilyBasic SpecialIntervalLimitLaws SpecialIntervalZeroFamilies CantorSplitRadius EqualSpacingContainedSum SpecialIntervalClipping ClassicalCantorSplit EqualCostIntervalFamilyUP SpecialIntervalLimit SpecialIntervalRefinement EqualCostIntervalEnumeration EqualCostIntervalMesh EqualCostIntervalTreeUP SpecialIntervalRefinementRestriction SpecialIntervalTreeLevels EqualCostIntervalClipped EqualCostIntervalSpecial PowerCantorNull PowerCantorPairUP SpecialIntervalDescendants SpecialIntervalTreeUpperBound EqualCostIntervalFamily EqualCostIntervalTreeLaws SpecialIntervalTreeTopology EqualCostIntervalTreeSpecial SpecialIntervalTreeLowerBound SpecialIntervalTreeMass EqualCostIntervalTree EqualCostCantorMass ConcaveCantorFunction PowerCantorPair.

(** Supporting interfaces for Federer 2.10.29, pp. 193–195:
    interleaved scales, explicit-coefficient real power measures,
    interval agreement, packing and local mass bounds. The final
    higher Cartesian-power conclusions follow below. Source comments
    accompany each declaration; existence constructions stay private. *)
From Federer Require Export
  CantorRadiusHalving CantorSplitSmallSpacing EqualCostIntervalChildLaws EqualCostIntervalSpacing FiniteNoThreeCardinality InterleavedCantorScalesUP MetricRealPowerCost PowerCantorSplit ThreePointRealPacking EqualCostIntervalUniformWidths EqualWidthIntervalPacking InterleavedCantorScalesLaws MetricRealPowerIntervalHull MetricRealPowerMeasureUP SpecialIntervalLimitLocalBounds EqualCostIntervalTreeLinks MetricRealPowerMeasureLaws SpecialIntervalUniformLinearBound EqualCostTreeLinearBound InterleavedCantorScales InterleavedPowerCantorPairs MetricRealPowerMeasure MetricRealPowerClosedCovers MetricRealPowerIntervalLower MetricRealPowerIntervalUpper MetricRealPowerLength MetricRealPowerIntervalAgreement PowerCantorIntervalBounds.

(** Mixed-product infinity and actual Euclidean plane support
    for 2.10.29, p. 194. The higher Cartesian-power
    conclusion follows below.
    Source comments accompany the declarations. *)
From Federer Require Export
  CaratheodoryVanishingDensity PowerCantorProductScalar MetricCartesianRectangleBounds PowerCantorProductMeasure InterleavedCantorCutoffs PowerCantorProductCases InterleavedCantorProductDensity InterleavedCantorProductInfinite EuclideanRealPlane EqualCostIntervalCommonWidth.

(** Euclidean rectangle and level-cost support for 2.10.29,
    pp. 193–194, with the actual Euclidean mixed-product
    infinity theorem. These declarations use only the public
    specifications and have individual source comments. *)
From Federer Require Export
  EuclideanIntervalRectangles PowerCantorSquareCost PowerCantorLevelWeights EuclideanCantorProduct.

(** Finite self-products and the combined interleaved Cantor
    product counterexample of 2.10.29, pp. 193–194.
    The final higher Cartesian-power paragraph is separate.
    Source comments accompany the declarations. *)
From Federer Require Export PowerCantorSelfProduct PowerCantorProductCounterexample.

(** Supporting local density product laws and finite coordinate
    weight sums for the higher powers in 2.10.29, p. 195.
    The final Euclidean higher-power theorem follows below.
    Source comments accompany these declarations. *)
From Federer Require Export
  PowerCoverDensityUP PowerCoverDensityScalars PowerCoverDensityProduct PowerCoverDensityLaws FiniteFunctionPowerWeights EuclideanSetPowers.

(** Finite Euclidean cube covers and the sealed measure and
    set power interfaces for 2.10.29, p. 195. The product
    density and positive-mass laws are proved consequences.
    Source comments accompany the declarations; recursive
    witnesses and sealing implementations remain private. *)
From Federer Require Export
  EuclideanIntervalBoxes PowerCantorFinitePowers EuclideanMeasurePowerUP EuclideanMeasurePower EuclideanMeasurePowerRegular EuclideanBlockSetPowerUP EuclideanBlockSetPower EuclideanMeasurePowerMass EuclideanRealPlaneTopology.

(** Competing product regularity and the actual Euclidean
    higher mixed-power infinity theorem of 2.10.29, p. 195.
    The orthogonal coordinate rearrangement follows below.
    Source comments accompany the declarations. *)
From Federer Require Export EuclideanCantorProductRegular InterleavedCantorInfinitePowers.

(** Orthogonal coordinate regrouping, real power-gauge isometry
    and the full positive-integer Cartesian-power product
    conclusions of 2.10.29, p. 195. Normalising coefficients
    remain explicit. Source comments accompany the declarations;
    the coordinate construction and sealing module stay private. *)
From Federer Require Export
  EuclideanHeadTailGeometry EuclideanSetPowerCoordinates EuclideanPairPowerShuffleUP EuclideanPairPowerShuffle MetricRealPowerMaps CantorPowerProductTheorem.

(** Federer 2.10.30, p. 195: abstract normal-line
    symmetrisation, its proved existence and basic geometric
    consequences. Euclidean volume preservation is exported below.
    Source locators accompany every mathematical declaration;
    existence witnesses and their sealing modules remain private. *)
From Federer Require Export
  CenteredSectionUP CenteredSectionLaws ScalarBoundedLength CenteredSection CenteredSectionBounds UnitNormalGeometry SteinerSymmetrisationUP SteinerSymmetrisationLaws UnitNormalMetric NormalLineLength SteinerSymmetrisation UnitNormalTopology CompactScalarProductSections CompactCenteredProduct NormalBallSections SteinerBallBounds SteinerSphereBoundary NormalProductCoordinates SteinerCompact ScalarConvexSectionLength ScalarMinkowskiWidths NormalSectionConvex CenteredSectionMinkowski SteinerConvex EuclideanNormalChartUP.

(** Further consequences of the defining section laws in
    Federer 2.10.30, p. 195, including the orthogonal-chart
    volume proof and actual closed-ball boundary formulation.
    Source comments accompany every declaration. *)
From Federer Require Export
  EuclideanNormalChart EuclideanLastAxisLine EuclideanNormalBlockCoordinates EuclideanNormalBlockMeasure SteinerVolume MetricBallBoundary NormalReflectionBoundary SteinerBoundary SteinerNormalLines CenteredSectionDegenerate SteinerTheorem.

(** Normal-choice independence for the hyperplane operation in
    Federer 2.10.30, p. 195. These files contain annotated
    consequences of the abstract section and inner-product laws. *)
From Federer Require Export UnitNormalUniqueness ScalarReflectionMeasure CenteredSectionReflection SteinerNormalChoice.

(** Federer 2.10.31, pp. 195–196: the compact-family
    ball theorem. Radius witnesses remain private; the
    proofs use only the opaque least-radius laws.
    The local correction of the printed shrinking-ball
    centre has a separate checked counterexample.
    Source locators accompany the mathematical declarations. *)
From Federer Require Export
  CompactEnclosingRadiusUP CompactEnclosingRadiusLaws CompactEnclosingRadius CompactEnclosingRadiusHausdorff CompactEnclosingRadiusZero CompactEnclosingRadiusSingleton CompactFamilyMinimumRadius SteinerStableFamilyUP SteinerRadiusCenterCorrection SteinerChordReflection NormalReflectionBallImage SteinerMissingCap SteinerFiniteCaps MetricClosedSeparation CompactScalarLengthGap CenteredSectionFullInterval SteinerSphereCover SteinerMinimalSphere SteinerMinimalRadialSegments SteinerMinimalBall SteinerFamilyBallTheorem.

(** Federer 2.10.32, pp. 196–197: the sharp
    exterior-product volume bound, through Steiner-stable
    compact families and the abstract compact exhaustion.
    Source locators accompany every mathematical declaration.
    The exhaustion construction and sealing implementation
    remain private. *)
From Federer Require Export
  CenteredSectionChordRealisation SteinerConvexChordRealisation ExteriorParallelShifts ExteriorParallelAffinity NormalHyperplaneTopProduct NormalExteriorDoubleDifference DoubleDifferenceSeminorm NormalExteriorNormBound NormalEndpointDifferences SteinerExteriorEndpointBound SteinerExteriorDiameterBound SteinerExteriorCost HausdorffEndpointTransport ProductCoordinateConvergence HausdorffClosedEndpointBounds HausdorffExteriorBounds HausdorffOpenContainment HausdorffVolumeBounds SteinerVolumeCostFamilyUP SteinerVolumeCostFamilyClosed SteinerVolumeCostFamilyStable EuclideanBallExteriorCost SteinerVolumeCostComparison CompactExteriorCostFinite CompactConvexExteriorVolumeBound CompactConvexExhaustionUP CompactConvexExhaustionLaws CompactConvexExhaustion ClosedConvexExteriorVolumeBound EuclideanExteriorVolumeTheorem.

(** Federer 2.10.33, p. 197: the isodiametric corollary. Individual
    source locators accompany the declarations in EuclideanIsodiametric.v. *)
From Federer Require Export EuclideanIsodiametric.

(** Federer 2.10.34, p. 197: Gross measure is bounded by exterior-
    diameter measure. Source locators accompany the declarations. *)
From Federer Require Export ExteriorProjectionDiameter ProjectedExteriorGaugeBound GrossExteriorComparison.

(** Federer 2.10.35, p. 197: equality of all seven Euclidean measures.
    Individual source locators and the supporting abstract-interface
    arguments accompany the declarations in the following modules. *)
From Federer Require Export
  EuclideanLebesgueDensity EuclideanSphericalLebesgue EuclideanHausdorffLebesgue
  FullDimensionProjections CaratheodoryGeneratorMeasureBound FullDimensionProjectedVolume
  EuclideanExteriorLebesgue NonnegativeExtendedProbabilityConstant FullDimensionProjectionNorm
  InnerClosedBallConvex EuclideanConvexProjectionLebesgue FullDimensionIntegralGauge
  EuclideanIntegralGeometricLebesgue EuclideanMeasureEqualities.

(** Federer 2.10.36, p. 198: the factorial endpoint-product bound
    for arbitrary convex Euclidean sets. Source locators accompany
    every supporting declaration; only existing abstract objects are used. *)
From Federer Require Export
  CenteredSectionChordInclusion InnerCompactConvexHull EuclideanBipyramidSections
  UniformPrimitiveReflection BipyramidPowerIntegral BipyramidHatIntegral
  EuclideanHeadSectionIntegral UnitBipyramidVolumeBound BipyramidHeightVolumeBound
  NormalHeadChartGeometry SteinerChordVolumeBound EuclideanHeadExteriorBound
  ConvexEndpointVolumeBound.

(** Federer 2.10.37, p. 198: exterior-diameter measure is bounded
    by alpha(m) 2^(-m) m! times Q_t^m. Every declaration has an
    individual source locator and uses the existing abstract interfaces. *)
From Federer Require Export
  SimpleProjectionExponentNorm ConvexIntegralEndpointBound ExteriorIntegralGaugeBound
  ExteriorMeasureWeightedComparison ExteriorConvexIntegralComparison.

(** Federer 2.10.38, pp. 198–199: rectangular boxes enclosing
    nonempty compact sets, decreasing widths and all prefix exterior
    norm equalities. The frame implementation is sealed; the empty-source
    qualification is proved separately. Every declaration has its locator. *)
From Federer Require Export
  CompactDiameterPair CompactLinearChordMaximum EuclideanHeadExteriorFactor
  GreedyChordFrameUP GreedyChordFrameLaws TriangularExteriorScaling
  GreedyChordFrameExpansion GreedyChordExteriorProducts GreedyChordCoordinateBounds
  EuclideanBoxUP EuclideanBoxLaws GreedyChordEnclosingBox GreedyChordFrame
  CompactEnclosingBox GreedyChordDegenerateCases EmptyCompactBoxCounterexample.

(** Federer 2.10.39, p. 199: spherical measure is bounded by
    n^(m/2) 2^(m-1) times exterior measure, for every positive
    degree and arbitrary targets. Interval nodes, counts and grid
    centres are sealed. All declarations carry individual source locators. *)
From Federer Require Export
  ScalarSubdivisionCount ScalarIntervalPartitionUP ScalarIntervalPartitionLaws ScalarIntervalPartition
  EuclideanCubeRadius RectangularGridUP RectangularGrid RectangularGridCardinality RectangularGridBallCover
  BoxSubdivisionCountsUP BoxSubdivisionCountsLaws BoxSubdivisionCounts PositiveBoxMeshBudget
  SphericalFiniteBallCover FiniteProductEnlargement GreedyChordDiameterBound
  PositiveRectangularSphericalCover RectangularSphericalCover CompactExteriorSphericalCutoff
  SphericalExteriorComparison EuclideanAboveDimensionNull SphericalExteriorTheorem.

(** Federer 2.10.40, pp. 199–200: a compact positive-radius
    family has a unique minimum-scale centre in the convex hull
    of its contact centres. The minimum witness is opaque;
    uniqueness and contact geometry are consequences of its laws.
    Individual declarations carry precise source locators. *)
From Federer Require Export
  WeightedBallMinimumUP CompactNestedIntersection CompactPositiveScalarBounds
  WeightedBallFeasibleLaws WeightedBallParameterBounds WeightedBallMinimumLaws
  WeightedMidpointScale WeightedBallMinimumUniqueness WeightedBallMinimum
  WeightedBallContactProfiles WeightedBallContactCompact InnerUnitPerturbationSquare
  WeightedBallContactNonempty WeightedBallPerturbation CompactHullDirectionalCriterion
  WeightedBallDirectionalContact WeightedBallMinimumGeometry WeightedBallMinimumTheorem
  WeightedBallDegenerateCases.

(** Federer 2.10.41, p. 200: Jung's theorem for arbitrary
    positive finite-diameter Euclidean sources, with unique
    minimum-diameter closed ball and exact sharp coefficient.
    The finite-support and distance calculations are proved
    locally; individual declarations have source locators. *)
From Federer Require Export
  ConvexHullFiniteSupport JungWeightedDistances EuclideanUnitRadiusParameters
  JungConstant EuclideanMinimumBallUP EuclideanMinimumBallLaws JungContactBound
  CompactJungBall MinimumBallClosure BoundedJungBall JungTheorem.

(** Federer 2.10.42, p. 201: Jung's spherical/Hausdorff
    measure comparison, with arbitrary targets and infinite
    mass. The current interfaces use natural degrees,
    including zero. Each declaration has a source locator. *)
From Federer Require Export
  SphericalCutoffContainingBall JungSphericalCutoff JungSphericalComparison JungSphericalTheorem.

(** Federer 2.10.43, p. 201: Kirszbraun's theorem with exact
    preservation of the optimal Lipschitz constant. The finite
    prescribed-ball, weighted variance and maximal-graph arguments
    are proved locally. Only the opaque extension laws expose
    the selected witness; each declaration has a source locator. *)
From Federer Require Export
  CompactClosedFamilyIntersection InnerWeightedVariance PositiveWeightedBudget
  KirszbraunWeightedScale KirszbraunBallParameters KirszbraunFiniteBalls
  EuclideanClosedBallCompact KirszbraunOnePoint KirszbraunExtensionUP
  KirszbraunExtensionLaws NonexpandingGraph KirszbraunGraphOnePoint
  EuclideanTargetScaling KirszbraunExtension KirszbraunTheorem.

(** Federer 2.10.44, p. 202: the printed non-inner-product
    norm counterexample and arbitrary-metric scalar extension,
    including the infimum formula on nonempty sources. Norm,
    map and envelope witnesses are opaque; all named declarations
    carry individual source locators and qualifications. *)
From Federer Require Export
  McShaneEnvelopeUP McShaneEnvelopeLaws McShaneCostBounds McShaneEnvelope
  EmptyMcShaneSource McShaneExtensionTheorem PlaneSupremumNormUP PlaneSupremumNormLaws
  PlaneSupremumNorm PlanePairNormGeometry PlaneSupremumNoninner KirszbraunCorners
  KirszbraunCornerMapUP KirszbraunCornerMap KirszbraunCornerDistances
  EquilateralUnitBallsEmpty KirszbraunCornerIsometry KirszbraunCornerNonextension KirszbraunCounterexample.

(** Federer 2.10.45, pp. 202–203: Euclidean-factor Hausdorff
    product measure and coefficient bounds, for natural degrees.
    Arbitrary metric second factors, zero mass, zero dimensions
    and all Lebesgue-measurable first factors are included.
    Mesh counts are used only through their opaque interface. *)
From Federer Require Export
  SquaredMetricProductUP SquaredMetricProductLaws MetricProductRectangles HausdorffProductSliceMeasure
  SquaredProductDiameter UniformMeshCountUP UniformMeshCountLaws UniformMeshCount
  EuclideanSquaredProduct EuclideanProductTranslation HausdorffIsometricBijection HausdorffProductSliceTranslation
  HausdorffRectangleLowerBound HausdorffCutoffFiniteCover EuclideanProductCoefficient EuclideanCubeProductFiniteCover
  ScaledMetricEnvelopeBound PositiveMeshCostLimit EuclideanCubeProductGeneratorBound MetricRectangleSliceMeasure
  EuclideanCubeProductCutoffBound PolynomialMarginLimit EuclideanCubeProductUpperBound BorelRegularisationBijection
  BorelMeasureCompletionAgreement EuclideanCoordinateCubeLaws HausdorffProductSliceHaar HausdorffProductBorelMultiple
  BorelScaledCompletionAgreement HausdorffProductMeasurableMultiple HausdorffProductNullFactor EuclideanProductCoefficientBounds
  HausdorffEuclideanProduct EuclideanProductCoefficientNormalisation HausdorffEuclideanProductTheorem.

(** Federer 2.10.46, pp. 203–204: checked supporting
    projection factors, opaque adapted charts, outer-volume
    estimates and the finite-positive-factor Gross upper bound.
    This is partial coverage: the full product identities and
    remaining endpoint cases are not claimed here. *)
From Federer Require Export
  EuclideanRightBlockProjection EuclideanProductProjectionFactor ProductProjectionImage
  OrthogonalProjectionChartUP OrthogonalProjectionChartLaws OrthogonalProjectionChart
  ProjectionChartFubini ProjectionChartFibres ProjectionSectionVolumeBound
  OrthogonalProjectionVolumeBound ProductProjectedVolumeBound BallProductProjectedGauge
  RectangleScaleSecondFactor EuclideanRectangleBorel GrossBallProductCutoff
  SmallBallLebesgueComparison GrossFiniteProductUpper.

(** Further endpoint coverage of the same partial item:
    null second factors in every first dimension, and the upper
    bound for arbitrary first volume with finite second mass. *)
From Federer Require Export MetricRectangleFirstSlice GrossProductNullFactor GrossProductUpperBound.

(** Further checked parts of 2.10.46: the closed-convex
    Caratheodory upper bound, the Gross lower bound from Borel
    partitions, and the Gross equality on completed measurable
    factors with finite second mass. The unrestricted Gross identity is exported below; the
    integral-geometric assertion remains pending. *)
From Federer Require Export EuclideanRectangleConvex ConvexBallProductCutoff
  ConvexFiniteProductUpper ConvexProductNullFactor ConvexProductUpperBound
  EuclideanBlockProjection ProductProjectedGaugeLower GrossBorelProductLower
  GrossFiniteBorelProduct GrossBorelProduct BorelRectangleFirstSlice
  GrossMeasurableProduct GrossCompletedProduct ProjectionProductEmptyBlock
  ProjectionProductUpperBounds.

(** Federer 2.10.46, p. 204: remove measurability
    assumptions from the Gross identity when the second mass
    is finite, using finite rectangles and Borel hulls. *)
From Federer Require Export NonnegativeIntegralSetBound RegularProductRectangleValue
  FiniteBorelMeasureAgreement BorelProductMeasureBound GrossFiniteRectangleMeasure
  GrossFiniteOuterProduct GrossArbitraryProduct.

(** Federer 2.10.46, p. 204: include infinite second mass
    for Lebesgue-measurable first and Borel second factors,
    retaining the ordinary defined-product domain. *)
From Federer Require Export GrossInfiniteSecondProduct.

(** Federer 2.10.46, p. 204: arbitrary first factors and Borel second factors, including infinite mass. *)
From Federer Require Export EuclideanRectangleMeasurableHull GrossBorelSecondProduct.

(** Federer 2.10.46, p. 204: arbitrary factors with a countable finite-measure cover of the second factor. *)
From Federer Require Export GrossSigmaFiniteProduct.

(** Federer 2.10.46, p. 204: the full Gross product identity,
    including arbitrary factors and infinite second mass on the
    ordinary defined-product domain of 2.1.1, p. 51. *)
From Federer Require Export ProductSectionOuterBound EuclideanSectionOuterBound ProjectedSectionGaugeLower GrossBorelSectionLower DynkinFamilyUP DynkinBorelCriterion BorelRectangleDynkin FiniteMeasureRealLaws FiniteSectionBaireFamily FiniteBorelSectionVolume GrossArbitraryInfiniteProduct.

(** Supporting Federer 2.10.46, p. 204: affine cylinder fibres and their actual integrals; the rotation average remains pending. *)
From Federer Require Export LineCylinderProjectionCoordinates AffineCylinderFibreCount FiniteSectionCountingIntegral ScalarAffineLebesgue ScalarAffineSections AffineCylinderFiniteIntegral AffineCylinderSectionIntegral AffineCylinderSectionLower FiniteProjectionFibres AffineCylinderNullSectionCounterexample AffineCylinderProductIntegral.

(** Supporting Federer 2.10.46: scalar cylinder coordinates and exceptional projection kernels. Source details accompany each declaration. *)
From Federer Require Export BijectionPrecompositionMultiplicity ScalarBlockMeasureBijection LineCylinderProjectionIntegral EuclideanProjectionKernelNull.

(** Supporting Federer 2.10.46: scalar cylinder coordinates and exceptional projection kernels. Source details accompany each declaration. *)
From Federer Require Export ProjectionKernelIncidence LineCylinderProjectionFactor.

(** Supporting Federer 2.10.46: scalar cylinder coordinates and exceptional projection kernels. Source details accompany each declaration. *)
From Federer Require Export ProjectionKernelProbability FiniteProjectionOrbit.

(** Supporting Federer 2.10.46: scalar cylinder coordinates and exceptional projection kernels. Source details accompany each declaration. *)
From Federer Require Export EuclideanBlockExtensionUP EuclideanBlockExtensionSealed EuclideanBlockExtension EuclideanBlockExtensionTopology.

(** Supporting Federer 2.10.46: scalar cylinder coordinates and exceptional projection kernels. Source details accompany each declaration. *)
From Federer Require Export EuclideanHomParameterContinuity EuclideanOrthogonalBlockExtension ProjectionMultiplicitySourceChange LineCylinderRotationIntegral.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export CompactContentPruning CompactLevelNeighborhood CompactContentSliceContinuity CompactContentDivisibility RefiningCoverContent HausdorffFinitePositiveSubsetBase.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export RestrictedCoverSplitting DyadicCubeGridUP DyadicCubeGridSealed DyadicCubeGrid DyadicCubeGridLaws RefiningContentStability FiniteNullOverlapAdditivity DyadicCubeRefinement DyadicCubeOverlap.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export DyadicContentSplitting.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export CompactCellRecombination TwoCellIntervalCover CompactCoordinateExtremes DyadicSmallSetCover.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export DyadicScaleBounds DyadicContentCutoffLower DyadicLevelCostBound DyadicPowerContentBound CompactPositiveUnitCube.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export DyadicPowerZeroBound DyadicPowerDiameterBound DyadicContentCutoffUpper RealPowerCompactCost RealPowerCompactScaleAgreement RealPowerCompactCutoff RealPowerNullNeighborhood DyadicContentFinite DyadicContentNullNeighborhood DyadicContentNullSets DyadicContentDivisibility.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export DyadicCompactPruningStep DyadicPruningUP RefiningContentIntervalStability DyadicPruningSealed DyadicPruning DyadicContentLimitBound.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export DyadicPruningIntersection DyadicNullSectionsCompactSubset.

(** Supporting Federer 2.10.47: refining covering contents and compact pruning. Source details accompany each declaration. *)
From Federer Require Export EuclideanHyperplaneGeometry CompactNullSectionsSubset RealPowerSingletonBound CompactHyperplaneReduction EuclideanPositiveCompactSubset RealPowerNaturalHausdorff RealPowerZeroCompactSubset HausdorffFinitePositiveSubset.

(** Supporting Federer 2.10.48: finite compact inner approximation of Suslin sets. Source details accompany each declaration. *)
From Federer Require Export FiniteCompactMassUP FiniteCompactMassSealed FiniteCompactSuslinInner RealPowerCompactLimit RealPowerSuslinPositiveCompact HausdorffFiniteCompactInner.
