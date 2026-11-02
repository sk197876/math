(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Basis-layer exports for Federer 1.3.1–1.3.2. Each mathematical claim
    is indexed in docs/chapter1.md and numbered in the source comments. *)
From Federer Require Export ExteriorCore
  LinearBasis TensorBasis GradedBasis UnitalGradedTensor
  ExteriorDirectSum ExteriorSmall FiniteCoordinates ExteriorIndices
  FiniteExteriorBasis FiniteExteriorPowers FiniteDimension CountableExteriorBasis.
