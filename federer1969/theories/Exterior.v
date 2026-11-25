(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Public entry point for Federer 1.3.1–1.3.4. Each mathematical claim
    is indexed in docs/chapter1.md and numbered in the source comments. *)
From Federer Require Export ExteriorBases
  TensorAssociator GradedTensorAssociator UnitalTensorSymmetry
  ExteriorDiagonal ExteriorCoassociativity Shuffles
  InversionCount ExteriorShuffleExpansion ShuffleSums
  ShuffleTransport ExteriorShuffleFormula.
From Federer Require Export
  OrderedIndices ExteriorPermutation ExteriorExpansion
  ExteriorDeterminant PermutationDeterminant ExteriorLeibniz.
