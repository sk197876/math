(** Federer (1969), 4.1.15, pp. 372–373: flat images depend
    only on a map's values on the actual current support.
    The radial smoothing proof yields retraction localisation,
    both point-support cases, section-image equalities and
    the arbitrary affine-plane obstruction. The actual finite-mass
    point one-current and compact smooth oscillating tests show
    why the flat hypothesis is required. *)
From Federer Require Export RadialShrinkMapUP RadialShrinkMapSealed
  RadialShrinkMapDisplacement RadialShrinkMapNorm RadialShrinkMapPairSquares
  RadialShrinkMapNonexpanding RadialAgreementMapUP RadialAgreementMapSealed
  RadialAgreementMapBounds RadialAgreementMapLipschitz
  SmoothingConvolutionLocalAgreement RadialAgreementNeighbourhood
  RadialSmoothingAgreement ClosedBallContainmentOpen RadialSmoothingLocusOpen
  RadialSmoothingErrorBound RadialSmoothingFamilies
  CurrentSupportSmoothComparisonUP CurrentSupportSmoothComparisonExistence
  CurrentFlatLipschitzSupportAgreement CurrentCompactRetractionExtension
  CurrentFlatLipschitzRetraction CurrentFlatLipschitzRetractionSet
  CurrentFlatIdentityPushforward CurrentFlatConstantPushforward
  CurrentFlatPointSupport CurrentFlatLipschitzSection CurrentFlatAffinePlaneSupport
  PointOneCurrent PointOneCurrentProduct PointOneCurrentBoundary PointOneCurrentImages
  PointOneCurrentNotFlat PointOneOscillatingMapsUP PointOneOscillatingMapsSealed
  PointOneOscillatingMapsBounds PointOneOscillatingScalarTests
  PointOneCurrentSequenceDivergence PointOneCurrentOscillation.
