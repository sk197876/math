(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Federer 1.4.5: public entry point, in the order of the book.
    Every assertion is proved or explicitly refuted by a checked
    counterexample; see docs/chapter1.md for the paragraph inventory. *)
From Federer Require Export DualExterior.
From Federer Require Export HomTensor Gamma DiagonalTensor DiagonalAlgebra
  TraceAlgebra TraceComponents GammaPower GammaIntrinsic GammaNaturality TraceDefinition
  AlgebraPowers AlgebraWordLaws SelectionPowers GammaProducts DividedPowers
  SharedIndices WordPairing LambdaComplements TraceBasisProduct TraceContraction
  TracePower AlgebraBinomial DividedBinomial CharacteristicPolynomial
  CharacteristicIdentities TraceCyclic TraceDual TraceUniqueness
  IndependentDual OrdinaryTensorObstruction OrdinaryTensorDimension
  OrdinaryTensorException.
