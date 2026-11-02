(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Federer 1.6.2: G(V,m), the surjective association from nonzero
    simple m-vectors, its fibres, the positive-scalar equivalence and
    the quotient G_o(V,m), with both Euclidean abbreviations. *)
From Federer Require Export SimpleVectors.
From Federer Require Export SubspaceEquality NonzeroSimple GrassmannSubspaces
  SubspaceBasisProduct GrassmannSurjection ScalarEquivalence PositiveEquivalence
  OrientedGrassmann GrassmannAbbreviations.
From Federer Require Export SimpleCovectors CovectorDimension CovectorBoundary.
From Federer Require Export SimpleAdaptedBasis.
From Federer Require Export DualitySimplicity.
From Federer Require Export DualityBoundary.
From Federer Require Export Annihilator.
From Federer Require Export AnnihilatorIntersection.
From Federer Require Export DualityAnnihilator.
From Federer Require Export AnnihilatorDimension.
From Federer Require Export SpanningDimension.
From Federer Require Export SubspaceSumDimension.
From Federer Require Export CovectorSimpleProducts.
From Federer Require Export ScaledSimpleCovectors.
From Federer Require Export IntersectionDuality.
From Federer Require Export CovectorProductNaturality.
From Federer Require Export SimplePairingDeterminant.
From Federer Require Export InteriorNaturality.
From Federer Require Export ProductSpaceMaps.
From Federer Require Export ProductContraction.
From Federer Require Export PairedExteriorWords.
From Federer Require Export InteriorFrame.
From Federer Require Export InitialComplementSequence.
From Federer Require Export InteriorBlock.
From Federer Require Export DualProductContraction.
From Federer Require Export ProductAdaptedWords.
From Federer Require Export FinalBlockDuality.
From Federer Require Export ProductAdaptedIdentity.
From Federer Require Export InteriorVanishing.
From Federer Require Export CovectorKernelProjection.
From Federer Require Export ProductMissingCovector.
From Federer Require Export BasisPairPartition.
From Federer Require Export BasisIndexFamilies.
From Federer Require Export ProductContractionAlgebra.
From Federer Require Export ProductVolumeChange.
From Federer Require Export ProductFourBlocks.
From Federer Require Export ProductBasisIdentity.
From Federer Require Export BilinearBasisExt.
From Federer Require Export ProductSpaceIdentity.
From Federer Require Export ScalarRestriction.
From Federer Require Export ComplexScalarUP.
From Federer Require Export ComplexScalarSealed.
From Federer Require Export ComplexScalarLaws.
From Federer Require Export ComplexCoefficientAlgebra.
From Federer Require Export ComplexAlternatingForms.
From Federer Require Export ComplexValuedForms.
From Federer Require Export ComplexFormSubspace.
From Federer Require Export FormCoefficients.
From Federer Require Export ComplexFormConjugation.
From Federer Require Export ComplexFormProducts.
From Federer Require Export ComplexConjugateProducts.
From Federer Require Export ComplexRealBasis.
From Federer Require Export ScalarRestrictionProduct.
From Federer Require Export BasisInSubspace.
From Federer Require Export ComplexAlgebraScalars.
From Federer Require Export ComplexAlternatingSum.
From Federer Require Export ComplexCharacteristic.
From Federer Require Export ComplexPairCoordinates.
From Federer Require Export FormBasisValues.
From Federer Require Export ComplexOneFormBasis.
From Federer Require Export ComplexOrderedBases.
From Federer Require Export ComplexCoordinateRestriction.
From Federer Require Export ComplexFormWords.
From Federer Require Export ComplexProductBasis.
From Federer Require Export ComplexMixedForms.
From Federer Require Export ComplexWordRestriction.
From Federer Require Export FormWordOperations.
From Federer Require Export ComplexTopVolume.
From Federer Require Export ComplexPullback.
From Federer Require Export FormPullbackProduct.
From Federer Require Export ComplexDeterminant.
From Federer Require Export ComplexBasisChange.
From Federer Require Export ComplexSubspaces.
From Federer Require Export ComplexFiniteSubspace.
From Federer Require Export PairedGradedWords.
From Federer Require Export ComplexPairedVectors.
From Federer Require Export ComplexSpanComparison.
From Federer Require Export ComplexPairedPlanes.
From Federer Require Export ComplexPairedNaturality.
From Federer Require Export ComplexPlaneOrientation.
From Federer Require Export ComplexSimpleVectors.
From Federer Require Export ComplexOrientation.
From Federer Require Export ComplexStarSubalgebra.
From Federer Require Export ComplexValuedProducts.
From Federer Require Export ComplexVolumeWords.

(** Federer 1.7.1: inner-product specifications and their proved consequences. *)
From Federer Require Export InnerProductUP.
From Federer Require Export BilinearPolarity.
From Federer Require Export InnerProductLaws.
From Federer Require Export InnerCauchy.
From Federer Require Export InnerNormUP.
From Federer Require Export InnerNormSealed.
From Federer Require Export InnerNorm.
From Federer Require Export IndependentPair.
From Federer Require Export InnerNormInequalities.
From Federer Require Export InnerPolarity.
From Federer Require Export OrthonormalFamilies.
From Federer Require Export EuclideanInnerProduct.
From Federer Require Export OrthonormalProjection.
From Federer Require Export InnerNormalization.
From Federer Require Export FiniteSpanTransfer.
From Federer Require Export FinitePrefixes.
From Federer Require Export OrthonormalExtension.
From Federer Require Export OrthonormalisationUP.
From Federer Require Export OrthonormalisationSealed.
From Federer Require Export GramSchmidt.
From Federer Require Export InnerMetric.
From Federer Require Export InnerNormedTopology.
From Federer Require Export InnerFiniteSynthesis.
From Federer Require Export InnerBoundedness.
From Federer Require Export InnerFiniteCompactness.
From Federer Require Export InnerOrthogonality.
From Federer Require Export InnerCompactDimension.
From Federer Require Export InnerCompactness.
From Federer Require Export OrthogonalMaps.
From Federer Require Export OrthogonalFinite.
From Federer Require Export OrthogonalEuclidean.
From Federer Require Export InnerPolaritySurjection.
From Federer Require Export InnerDualUP.
From Federer Require Export InnerDualSealed.
From Federer Require Export InnerDual.
From Federer Require Export InnerDualNorm.
From Federer Require Export InnerDualSupremum.
From Federer Require Export InnerDualBasis.
From Federer Require Export OrthogonalComplement.
From Federer Require Export SymmetricEndomorphisms.
From Federer Require Export PrincipalAxesUP.
From Federer Require Export PositiveSemidefinite.
From Federer Require Export InnerProductRestriction.
From Federer Require Export InnerRestrictedNorm.
From Federer Require Export BilinearDiagonal.
From Federer Require Export RayleighBound.
From Federer Require Export CompactMaximum.
From Federer Require Export InnerCoordinateContinuity.
From Federer Require Export BilinearFiniteCoordinates.
From Federer Require Export QuadraticContinuity.
From Federer Require Export ConstrainedUnitSphere.
From Federer Require Export ConstrainedSphereNonempty.
From Federer Require Export MaximalOrthonormalUP.
From Federer Require Export MaximalOrthonormalExtension.
From Federer Require Export SemidefiniteRestriction.
From Federer Require Export BilinearDifference.
From Federer Require Export RayleighSubspace.
From Federer Require Export RayleighStationary.
From Federer Require Export PrincipalAxisConstraint.
From Federer Require Export MaximalPrincipalAxes.
From Federer Require Export PrincipalAxesSealed.
From Federer Require Export PrincipalAxes.
From Federer Require Export OrthonormalSingleCoordinate.
From Federer Require Export EndomorphismBilinearForm.
From Federer Require Export PrincipalAxesDiagonal.
From Federer Require Export EigenbasisUP.
From Federer Require Export SymmetricEigenbasis.
From Federer Require Export InvariantRestriction.
From Federer Require Export OrthogonalSubspaceSplit.
From Federer Require Export MinimalInvariantUP.
From Federer Require Export InvariantFiniteSpan.
From Federer Require Export EigenvectorExistence.
From Federer Require Export SpanningDimensionBound.
From Federer Require Export MinimalSymmetricDimension.
From Federer Require Export CyclicPair.
From Federer Require Export MinimalSkewDimension.
From Federer Require Export SubspaceDimensionOrder.
From Federer Require Export MinimalInvariantExistence.
From Federer Require Export InvariantOrthogonalSplit.
From Federer Require Export OrthogonalDecompositionUP.
From Federer Require Export OrthogonalDecompositionExtension.
From Federer Require Export OrthogonalDecompositionSealed.
From Federer Require Export OrthogonalDecomposition.
From Federer Require Export OrthogonalImageBasis.
From Federer Require Export AdjointUP.
From Federer Require Export OrthonormalCapacityExtension.
From Federer Require Export AdjointSealed.
From Federer Require Export Adjoint.
From Federer Require Export AdjointLaws.
From Federer Require Export BasisInterpolation.
From Federer Require Export FinitePredicatePartition.
From Federer Require Export PartialOrthonormalCompletion.
From Federer Require Export OrthogonalBasisCriteria.
From Federer Require Export PolarFactorisationUP.
From Federer Require Export PolarInjectionSealed.
From Federer Require Export PolarInjection.
From Federer Require Export PolarProjection.
From Federer Require Export TwoFormBilinear.
From Federer Require Export BilinearRepresentation.
From Federer Require Export OrthonormalPairCoordinates.
From Federer Require Export SkewOneDimensional.
From Federer Require Export SkewPairUP.
From Federer Require Export SkewTwoDimensional.
From Federer Require Export MinimalSkewBlocks.
From Federer Require Export BilinearNegation.
From Federer Require Export SkewNormalFormUP.
From Federer Require Export SkewPairCoordinates.
From Federer Require Export OrthonormalPairExtension.
From Federer Require Export SkewNormalFormExtension.
From Federer Require Export SkewNormalFormSealed.
From Federer Require Export TwoCovectorProduct.
From Federer Require Export FormEvaluation.
From Federer Require Export AlternatingTwoNormalForm.
From Federer Require Export OrthogonalDecompositionUniqueness.
From Federer Require Export PolarKernelOrthogonality.
From Federer Require Export AdjointCriteria.
From Federer Require Export AdjointPolarity.
From Federer Require Export ProjectionCriteria.
From Federer Require Export IntersectionDimensionBound.
From Federer Require Export LinearRangeBasis.
From Federer Require Export OrthogonalEmbedding.
From Federer Require Export ProjectionRange.
From Federer Require Export CommonProjectionFactor.
From Federer Require Export BilinearPrecompose.
From Federer Require Export CoordinateProjection.
From Federer Require Export IndependentMap.
From Federer Require Export CoordinateProjectionVolume.
From Federer Require Export CoordinateProjectionSubspace.
From Federer Require Export AdjointIdentities.
From Federer Require Export InnerExteriorUP.
From Federer Require Export InnerExteriorSealed.
From Federer Require Export InnerExterior.
From Federer Require Export InnerExteriorProducts.
From Federer Require Export OrthonormalBilinearCoordinates.
From Federer Require Export InnerExteriorBasis.
From Federer Require Export InnerExteriorNaturality.
From Federer Require Export ExteriorPairReduction.
From Federer Require Export InnerExteriorPositivity.
From Federer Require Export ExteriorNorm.
From Federer Require Export InnerExteriorPolarity.
From Federer Require Export InnerExteriorIsomorphism.
From Federer Require Export ExteriorCovectorInnerUP.
From Federer Require Export ExteriorCovectorInnerSealed.
From Federer Require Export ExteriorCovectorInner.
From Federer Require Export ExteriorProductFactors.
From Federer Require Export ExteriorHadamardCorrection.
From Federer Require Export DependentPair.
From Federer Require Export InnerCauchyEquality.
From Federer Require Export ExteriorPairingBound.
From Federer Require Export InnerExteriorTriangular.
From Federer Require Export InnerExteriorDiagram.
From Federer Require Export ExteriorCovectorIdentification.
From Federer Require Export GramSchmidtTriangular.
From Federer Require Export GramSchmidtExteriorFactor.
From Federer Require Export FiniteProductEquality.
From Federer Require Export ExteriorHadamardBound.
From Federer Require Export ExteriorHadamardEquality.
From Federer Require Export InnerExteriorIndexProducts.
From Federer Require Export ExteriorBasisWedgeNorm.
From Federer Require Export SimpleOrthonormalBasis.
From Federer Require Export FiniteSimpleWedgeNorm.
From Federer Require Export ExteriorNormNaturality.
From Federer Require Export SimpleWedgeNorm.
From Federer Require Export SimpleOrthonormalFactor.
From Federer Require Export OrthonormalConcatenation.
From Federer Require Export OrthonormalWedgeEquality.
From Federer Require Export ProductAssociatedOrthogonality.
From Federer Require Export SimpleWedgeEquality.
From Federer Require Export ExteriorIndexSupport.
From Federer Require Export ExteriorBasisWedgeCoordinates.
From Federer Require Export ExteriorIndexSupportCard.
From Federer Require Export FiniteSumCauchy.
From Federer Require Export FiniteSparseSumBound.
From Federer Require Export OrthonormalParseval.
From Federer Require Export BilinearDoubleExpansion.
From Federer Require Export ExteriorWedgeCoordinateExpansion.
From Federer Require Export FiniteWedgeNormBound.
From Federer Require Export ExteriorWedgeNorm.
From Federer Require Export FiniteOrdinalBasis.
From Federer Require Export ExteriorPolarityMetric.
From Federer Require Export InnerExteriorLowDegrees.
From Federer Require Export TriangularProductChange.
From Federer Require Export FiniteFamilyOrthogonalSplit.
From Federer Require Export OrthogonalResidualFamily.
From Federer Require Export OrthogonalResidualProducts.

(** Federer 1.7.6: adjoints, exterior powers, and operator norms.
    Mathematical source annotations are in the exported modules. *)
From Federer Require Export AdjointDeterminant.
From Federer Require Export AdjointTrace.
From Federer Require Export ExteriorAdjoint.
From Federer Require Export ExteriorAdjointConsequences.
From Federer Require Export ExteriorMapScaling.
From Federer Require Export OperatorNorm.
From Federer Require Export OperatorNormAdjoint.
From Federer Require Export OperatorNormLaws.
From Federer Require Export OperatorNormSealed.
From Federer Require Export OperatorNormUP.
From Federer Require Export OrthogonalExteriorImages.
From Federer Require Export ExteriorOperatorEstimate.
From Federer Require Export OperatorNormTransport.
From Federer Require Export OperatorDualNorm.
From Federer Require Export ExteriorOperatorNorm.
From Federer Require Export ExteriorCovectorBasis.
From Federer Require Export ExteriorCovectorOperatorNorm.
From Federer Require Export TopExteriorNorm.
From Federer Require Export TopExteriorInjectivity.
From Federer Require Export AdjointSurjectivity.
From Federer Require Export TopTargetExteriorNorm.
From Federer Require Export OperatorNormIdentities.

(** Federer 1.7.7: projection suprema; precise sources accompany the declarations. *)
From Federer Require Export CovectorProjectionNorm
  ExteriorFrameUnitNorm
  ExteriorProjectionNorm
  FrameImageSpan
  NonnegativeSupremum
  OrthonormalFrameMap
  ProjectionNorm
  SimpleCovectorProjectionSupremum
  SimplePolarityTransfer
  SimpleProjectionAttainment
  SimpleVectorProjectionSupremum.

(** Federer 1.7.8: Hodge star; source and erratum locators accompany the declarations. *)
From Federer Require Export HodgeAlgebraCompatibility
  HodgeBasis
  HodgeComplement
  HodgeIsometry
  HodgeMaps
  HodgeMixedPairing
  HodgePairing
  HodgePairingBasis
  HodgeReverseBasis
  HodgeSignedDuality
  HodgeSquare
  HodgeWedge
  HodgeWedgeBasis
  UnitTopVolume.

(** Federer 1.7.9: tensor and Hom metrics; source locators accompany the declarations. *)
From Federer Require Export HomOrthogonalChange
  OneCovectorOrthogonal
  TensorMapIsomorphism
  TopHomDeterminant
  ExteriorHomInner
  HomNormDimensionBound
  HomNormBound
  TensorInnerEvaluation
  HomInnerTrace
  HomInnerCoordinates
  HomInner
  TensorInnerContraction
  InnerProductPullback
  HomInnerUP
  TensorInnerPositivity
  TensorInnerNaturality
  TensorInner
  TensorOrthonormalSpan
  TensorInnerUP
  HomOperatorNorm.

(** Federer 1.7.10: bilinear invariants; source locators accompany the declarations. *)
From Federer Require Export BilinearRepresentativeUP BilinearInvariants BilinearInvariantsIntrinsic.

(** Federer 1.7.11: source locators accompany the declarations. *)
From Federer Require Export ProductInnerUP
  ProductInner
  ProductLinearMaps
  ProductFiniteBasis
  ProductOrthonormalBasis
  SubspaceDifference
  ProductDiagonalNormalization
  UpperDualityNorm
  DiagonalExteriorNorm
  DualProductHodgeNorm
  ProductTopNorm
  ProductContractionNorm
  EmbeddedTopContractionNorm
  SubspaceProductInclusion
  SimpleUnitAssociatedLift
  HodgeProductOrientation
  SubspaceDifferenceNormBasis
  SubspaceDifferenceNorm.

(** Federer 1.7.12: exports of the annotated second exterior trace proofs. *)
From Federer Require Export
  TraceTwoRankOne
  TraceGammaProduct
  ExteriorTwoTrace
  AdjointSquareTrace
  ExteriorTwoAdjointTrace.

(** Federer 1.7.13: exports of the annotated Hilbert-space specifications
    and proofs; existence witnesses remain behind their sealed interfaces. *)
From Federer Require Export
  HilbertSpaceUP
  HilbertClosedIntersection
  InnerParallelogram
  InnerSetDistanceUP
  InnerSetDistance
  InnerConvex
  InnerNearSet
  InnerMidpointParallelogram
  InnerNearDiameter
  InnerNearestUP
  InnerNearestSubspace
  InnerNearIntersection
  HilbertNearest
  HilbertFunctionalUP
  LinearFunctionalKernel
  HilbertFunctionalFormula
  HilbertFunctional.

(** Federer 1.8.1: abstract mass/comass specifications, sealed norm
    interfaces, convex-hull and optimal-decomposition proofs, and product
    and map estimates. Each declaration has its own source annotation. *)
From Federer Require Export
  CoefficientSimplex
  CompactNearest
  ConvexCoefficientElimination
  ConvexCoefficientRelation
  ConvexHullUP
  ExteriorProductContinuity
  NearestConvexVariational
  PositiveCoefficientReduction
  ShuffleCardinalityBound
  SimpleUnitBall
  SimpleUnitContraction
  SubconvexCombinations
  ComassUP
  ConvexFiniteCombinations
  SimpleUnitConnected
  SimpleUnitFactors
  SubconvexReduction
  ComassBounds
  ComassSphereBound
  ComassZeroDegree
  SimpleUnitCompact
  SubconvexCompact
  ComassAttainment
  ComassEuclidean
  ComassHomogeneity
  ComassTupleBounds
  MassUP
  Comass
  ComassComparison
  ComassSimpleEquality
  ComassWedgeBound
  MassBounds
  MassDecompositionBound
  ComassEquality
  ComassSimpleWedgeBound
  MassEuclidean
  MassHomogeneity
  MassPairingBound
  ComassWedgeSymmetry
  MassConvexHull
  MassEquality
  MassPositiveConvexRepresentation
  Mass
  MassOptimalDecomposition
  MassComassMaps
  MassInfimum
  MassWedgeBound.

(** Federer 1.8.2: Hermitian products, complex Cauchy inequality,
    the coordinate two-form identity, Wirtinger's inequality with its
    exact equality criterion, and the factorial comass. Source locators
    are attached to the individual declarations. *)
From Federer Require Export
  BilinearTwoForm
  CommutingNilpotentPowers
  ComplexFrameDimension
  ComplexModulusUP
  HermitianUP
  InnerUnitEquality
  PairedBasisCardinality
  PairedComplexSpan
  PairedFormProducts
  PairedOrthonormalCoordinates
  PairedOrthonormalDimension
  TwoFormBlocks
  TwoFormPowers
  TwoFormVectorNormalForm
  WirtingerCoefficientProduct
  HermitianRealImaginary
  PairedRealVectors
  SkewNormalVectorActions
  StandardHermitian
  TwoFormNormalPowers
  TwoFormPowerNaturality
  WirtingerZeroDegree
  ComplexModulusSealed
  HermitianComplexLinearity
  NormalPowerPolarity
  PairedFirstScaling
  PairedVectorNaturality
  SkewNormalFullBasis
  StandardHermitianCoordinates
  ComplexModulus
  HermitianRotation
  NormalPowerUnitBound
  PositivePairedScaling
  ComplexUnitPhase
  HermitianPairedBasis
  HermitianPullback
  HermitianUnitPair
  StandardHermitianForm
  HermitianCauchy
  HermitianNormalCoefficients
  WirtingerBasisEquality
  HermitianCauchyEquality
  WirtingerPairedEquality
  WirtingerUnitForward
  WirtingerForward
  Wirtinger
  WirtingerComass
  WirtingerFiniteComass.

(** Federer 1.8.3: the displayed comass unit ball and its convexity.
    Extreme points are defined for the question in the source; no general
    classification is asserted. Individual declarations carry locators. *)
From Federer Require Export ComassUnitBall EuclideanComassBall.

(** Federer 1.8.4: attainment of mass, the annihilating-covector
    calculation, and multiplicativity for orthogonally supported factors
    when either is simple. Each declaration has its source locator. *)
From Federer Require Export
  AnnihilatingBlockPairing
  MassAttainment
  MassWedgeSymmetry
  PositiveSimpleOrthonormalFactor
  MassUnitAttainment
  OrthogonalBlockMass
  SimpleOrthogonalCalibration
  MassSphereAttainment
  OrthogonalSimpleMass
  OrthogonalMass
  OrthogonalMassInterface.

(** Federer 1.9.1: abstract and sealed symmetric algebras, graded
    universal properties, low powers and induced maps. Individual
    declarations carry precise source locators. *)
From Federer Require Export
  CommutativeWords
  GradedSymmetricUP
  SymmetricUP
  SymmetricAlgebraUP
  SymmetricSealed
  SymmetricAlgebra
  SymmetricGrading
  SymmetricLowPowers
  SymmetricMaps
  SymmetricPowerFunctor
  SymmetricPowerProducts.

(** Federer 1.9.2: see the source locators beside each declaration. *)
From Federer Require Export
  OrdinaryTensorMultiplication
  SymmetricLineBasis
  SymmetricMultiIndices
  SymmetricZeroSpace
  SymmetricDirectSum
  SymmetricIndexBounds
  SymmetricMonomials
  SymmetricCoordinateSplit
  SymmetricIndexRecursion
  SymmetricCoordinateBasis
  SymmetricIndexCardinality
  SymmetricCoordinateMonomials
  SymmetricMonomialBasis
  SymmetricDimension.

(** Federer 1.9.3: see the source locators beside each declaration. *)
From Federer Require Export
  SymmetricDividedMonomials
  SymmetricIndexSummation
  SymmetricPolarizationCoefficients
  SymmetricMonomialFactors
  SymmetricPolarizationIndex
  SymmetricMultinomial
  SymmetricPolarization.

(** Federer 1.9.4: see the source locators beside each declaration. *)
From Federer Require Export
  AlgebraPowerMaps
  SymmetricDiagonal
  SymmetricExponentBox
  SymmetricBoxFibres
  SymmetricCoassociativity
  SymmetricCounit
  SymmetricMultiBinomial
  SymmetricShuffleExpansion
  SymmetricBoxSums
  SymmetricDiagonalPowers
  SymmetricShuffleFormula
  SymmetricDiagonalMonomials
  SymmetricDiagonalBinomial
  SymmetricDiagonalFormula.

(** Federer 1.10.1: see the source locators beside each declaration. *)
From Federer Require Export
  SymmetricForms
  SymmetricFormPermutations
  SymmetricFormWords
  SymmetricFormExtension
  SymmetricFormIsomorphism
  SymmetricFormZero
  SymmetricFormSum
  SymmetricPairing
  SymmetricFormDual.

(** Federer 1.10.2: see the source locators beside each declaration. *)
From Federer Require Export
  SymmetricFormProduct
  SymmetricFormUnit
  SymmetricFormShuffle
  MixedTensorPairing
  MixedHomogeneousConvolution
  SymmetricMixedProduct
  BasisRescaling
  SymmetricMultiIndexAddition
  SymmetricBoxKronecker
  SymmetricUnitMultiIndices
  SymmetricExponentWords
  SymmetricMonomialCoordinates
  SymmetricDividedBasis
  SymmetricCoordinateDualBasis
  SymmetricCoordinateProducts
  SymmetricCoordinateOneForms
  SymmetricCoordinateUnit
  SymmetricDualMonomialProducts
  SymmetricDualMonomialBasis.

(** Federer 1.10.3: see the source locators beside each declaration. *)
From Federer Require Export
  SymmetricFormReindex
  SymmetricPairingSeparation
  SymmetricInteriorUP
  SymmetricRightInteriorHom
  SymmetricRightInterior
  SymmetricLeftInteriorHom
  SymmetricLeftInteriorDegree
  SymmetricLeftInterior
  SymmetricMonomialProducts
  SymmetricRightMonomialContraction
  SymmetricLeftMonomialContraction
  SymmetricInteriorMonomialFormulas.

(** Federer 1.10.4: see the source locators beside each declaration. *)
From Federer Require Export
  PolynomialCoefficientUniqueness
  HomogeneousPolynomialFunctions
  SymmetricPolynomialEvaluation
  SymmetricPolynomialInjectivity
  PolynomialFunctions
  GradedDegreeUP
  GradedDegreeSealed
  GradedDegree
  PolynomialRepresentations
  SymmetricPolynomialProduct
  SymmetricFiniteContraction
  PolynomialCoordinates
  PolynomialTaylorTerms
  PolynomialTaylorTermPolynomial
  PolynomialTaylorCoefficients
  PolynomialTaylorTransform
  PolynomialTaylor
  PolynomialTaylorDegree.

(** Federer 1.10.5: see the source locators beside each declaration. *)
From Federer Require Export
  RealNormUP
  SymmetricZeroDegreeDecomposition
  LinearGraphAdjoinValue
  SeminormAdjoinInterval
  SeminormAdjoinDomination
  HahnBanachSealed
  HahnBanach
  SeminormLineGraph
  SeminormNormingFunctional
  InnerSymmetricPolarity
  InnerSymmetricUP
  InnerSymmetricSealed
  InnerSymmetric
  SymmetricFiniteSupport
  SymmetricFiniteReduction
  SymmetricMonomialNaturality
  SymmetricBiorthogonalMonomials
  InnerSymmetricMonomials
  SymmetricNormalizedMonomials
  SymmetricMonomialGram
  InnerSymmetricBasis
  InnerSymmetricPositivity
  SymmetricInnerNorm
  SymmetricFormFamily
  SymmetricFamilyArguments
  SymmetricIteratedShuffle
  SymmetricOneFormFormula
  SymmetricUniformOneForms
  SymmetricOneFormProductFormula
  InnerSymmetricPermutationFormula
  SymmetricInnerProductBound
  SymmetricInnerPurePowers
  ExtendedSupremumUP
  ExtendedSupremumSealed
  SymmetricOperatorNormUP
  SymmetricOperatorNorm
  SymmetricTupleScaling
  RealNormNormalization
  SymmetricOperatorTupleBound
  SymmetricOperatorBoundary
  SymmetricOperatorProductBound
  SymmetricOperatorInteriorBound
  SymmetricDecompositions
  SymmetricDecompositionCosts
  SymmetricMassInfimumUP
  SymmetricMassInfimumSealed
  SymmetricProjectiveMass
  SymmetricProjectiveSeminorm
  SymmetricMassPairingBound
  SymmetricMassNormingForm
  SymmetricMassUP
  SymmetricMassDuality
  SymmetricFunctionalProduct
  SymmetricFunctionalMassBound
  RealSeminormOperations
  SymmetricProjectiveMaximality
  SymmetricMassProductBound
  FiniteBasisInnerWitness
  RealSeminormDifference
  FiniteNormUpperBound
  FiniteNormContinuity
  FiniteNormLowerBound
  BoundedFunctionalExtension
  FiniteBoundedRetraction
  SymmetricMassMapBound
  SymmetricFiniteMassPositivity
  SymmetricMassPositivity
  SymmetricDegreeZeroPairing
  SymmetricDegreeZeroMass
  SymmetricMassSealed
  SymmetricMass
  FiniteNormCompactness
  SymmetricWordExpansion
  SymmetricProductContinuity
  SymmetricUnitProducts
  SymmetricUnitProductsCompact
  SymmetricMassConvexHull
  SymmetricOptimalDecomposition
  PolynomialNormUP
  PolynomialNorm
  PolynomialNormHomogeneity
  PolynomialDiagonalNorm
  PolynomialFiniteNormBound
  PolynomialPolarizationNorm
  SymmetricMassProducts
  SymmetricMassConsequences
  SymmetricMonomialTuples
  ScalarDividedMultinomial
  PolynomialCoefficientNorm
  PolynomialWeightedNormBound
  SymmetricInnerLowDegrees
  SymmetricOneFormUnitBound
  SymmetricDualMonomialForm
  SymmetricMassTupleBound
  SymmetricMonomialNormBounds
  SymmetricAlgebraOneForms
  ExtendedSupremumPowers
  SymmetricOneFormPowers
  SymmetricOneFormPowerNorm
  HilbertBilinearMaximizers
  HilbertPairGeometry
  HilbertFormCompactness
  UnitProductFactors
  HilbertExtremalPair
  SymmetricFormListSlots
  HilbertWordMaximum
  HilbertWordPair
  HilbertWordDiagonal
  FiniteHilbertDiagonalMaximum
  SymmetricFormPostcompose
  HilbertDiagonalDominance
  HilbertPolynomialNorm.

(** Federer 1.10.6: see the source locators beside each declaration. *)
From Federer Require Export
  SymmetricFormInnerUP
  SymmetricFormInnerSealed
  SymmetricFormInner
  SymmetricFormInnerCoordinates
  ScalarInnerProduct
  SymmetricPolarityIsomorphism
  SymmetricPolarityMetric
  SymmetricNormalizedDualMonomials
  SymmetricFormHilbertBounds
  SymmetricWordFibres
  SymmetricWordFibreCount
  SymmetricFormOperatorHilbertBound
  SymmetricFormTensor
  SymmetricFormTensorCoordinates
  SymmetricFormWordSquares
  SymmetricHilbertOperatorComparison
  SymmetricGivenDualBasis
  SymmetricFunctionFibres.
