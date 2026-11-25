(** Public laws for Federer (1969), 4.1.9, pp. 363–364:
    the original homotopy and velocity, opaque deformation
    chain, both current and form homotopy identities,
    original compact test restatements, exact integral of
    weighted slice image measures and all affine mass
    estimates. Every assertion retains the original
    domains, degrees and support-cylinder properness.
    The exported interfaces hide existence witnesses;
    their annotated declarations give precise source locators. *)
From Federer Require Export
  CurrentHomotopyUP
  CurrentHomotopyClass
  CurrentHomotopyGeometry
  CurrentHomotopyDomain
  CurrentHomotopyTimeVelocity
  CurrentHomotopySliceClass
  CurrentHomotopyDifferential
  CurrentDeformationChainSealed
  CurrentHomotopyPositiveFormula
  CurrentHomotopyZeroFormula
  CurrentHomotopyTransgressionSealed
  CurrentHomotopyTransgressionVelocity
  CurrentHomotopyPositiveFormFormula
  CurrentHomotopyZeroFormFormula
  CurrentHomotopyPositiveTestFormula
  CurrentHomotopyZeroTestFormula
  CurrentHomotopyIntegralMeasureUP
  CurrentHomotopyIntegralMeasureSealed
  CurrentHomotopyIntegralMeasureLaws
  CurrentAffineHomotopyMass
  CurrentSegmentPartialIntegral.
