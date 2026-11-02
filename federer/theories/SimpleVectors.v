(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Federer 1.6.1: simple m-vectors, their associated subspace T,
    the basis factorisation and all four corollaries. The literal
    degree-zero exception to the first corollary is proved explicitly. *)
From Federer Require Export InteriorDecomposition.
From Federer Require Export SubspaceCarrier FiniteSpans AssociatedSubspace
  SimpleZeroDegree ExteriorSubspaceReduction FiniteSpanSpace ExteriorFiniteReduction
  FiniteBasisExtension SingleIndexContraction AbsentBasisProducts InitialIndices
  InitialBasisProducts AssociatedInitialCoordinates AssociatedInitialFactor
  BoundedIndependentBasis SubspaceFamilies FiniteBasisComparison
  AssociatedFiniteFamily AssociatedDimension SimpleWordIndependence SimpleProducts
  SimpleElementary SimpleAssociatedBasis FullDegreeFactor AssociatedFactorInclusion
  SimpleInclusion SimpleProportionality BasisSizeTransport SimpleDimensionCriterion
  ConcatenatedFamilies IndependentProducts IndependentConcatenation
  SubspaceDirectSums ConcatenatedProducts SimpleDirectSum SimpleBoundary.
