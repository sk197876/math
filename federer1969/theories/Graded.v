(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Public entry point for Federer 1.2. *)
From Federer Require Export Tensor Bilinear AlgebraUP GradedAlgebra WordAlgebra
  TensorAlgebra TensorGrading TensorPowers TensorAlgebraMaps AlgebraTensor.
From Federer Require Export GradedSums TensorBilinear Koszul GradedTensor
  GradedTensorProduct GradedTensorLaws GradedTensorMaps GradedMultiplication
  GradedUnit GradedTensorFunctor.
From Federer Require Export GradedComponents GradedStructure GradedTensorUP
  TensorPowerComponents TensorPowerProduct.
