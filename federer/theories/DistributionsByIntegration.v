(** Federer (1969), 4.1.5, pp. 349–350: the original
    scalar-test gauge, its compact continuous convolution
    extension, exact normalized Radon representation and
    unique L1 extension. The public laws also give the
    simultaneous original ball formula, scalar Daniell
    variation, weak lower semicontinuity and the original
    monotone-bound weak compactness theorem.

    The literal final topology is retained. The gauge is
    defined on K(U)+ before any measure is introduced;
    its Radon identification is proved in the finite case. *)
From Federer Require Export DistributionVariationUP DistributionVariationSealed
  DistributionVariationBasic DistributionVariationScaling DistributionVariationDomain
  DistributionFiniteVariationUP DistributionContinuousExtensionUP DistributionContinuousExtensionSealed
  DistributionExtensionSharpBound DistributionSubspaceVariation
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  DistributionIntegrationCriterion FiniteDistributionRadonRepresentation
  DualLoneIntegralUP DualLoneIntegralSealed DualLoneIntegralAlgebra
  DistributionLoneExtension DistributionOriginalBallFormula
  ScalarDaniellDistribution ScalarDaniellDistributionVariation
  DistributionWeakLowerSemicontinuity DistributionMonotoneWeakCompactness.
