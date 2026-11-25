(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Public entry point through Federer 1.4.4. The scalar statements and
    the relative exterior algebra are proved. Three errors in the printed
    coefficient parenthesis are recorded by checked counterexamples; see
    docs/chapter1.md for the precise correspondence. *)
From Federer Require Export AlternatingCoordinates
  BasisMap
  CentralTensor
  CoefficientCoordinates
  DisjointBlocks
  ExteriorFiniteSupport
  FiniteEvaluation
  FirstArgument
  InfiniteSequence
  OneFormIdentification
  PartialLinearMap
  BlockCovector
  LinearExtension
  OmegaConstruction
  OneFormCommutator
  RelativeExterior
  CoefficientAction
  CoefficientImage
  LinearRetraction
  NoncommutativeObstruction
  OmegaFinite
  OmegaNaturality
  RelativeGeneration
  RelativeModule
  AlternatingCoefficientMap
  CoefficientCounterexample
  CountableRetraction
  FiniteEvaluationMaps
  OmegaComponents
  TensorEvaluation
  FiniteRankPullback
  OmegaInjective
  ZeroDimensionalCoefficients
  CountableNonSurjectivity
  RelativeOmega
  OmegaInfinite
  RelativeOmegaFinite.
