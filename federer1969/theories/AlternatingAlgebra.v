(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Public entry point through Federer 1.4.2. The claim-by-claim
    correspondence is recorded in docs/chapter1.md. *)
From Federer Require Export Alternating
  AlternatingFamily AlternatingProduct AlternatingShuffle
  AlternatingUnit BlockIndex Convolution
  ConvolutionAssociativity ConvolutionCommutativity ConvolutionNaturality
  ExteriorCounit FamilyArguments GradedConvolution
  IteratedShuffle MultipleShuffleBijection MultipleShuffleSums
  MultipleShuffles NonemptyProduct OneDegreeShuffles
  OneFormFormula PermutationArguments PermutationBlocks
  ShuffleComposition ShuffleDecomposition ShuffleUniqueness
  SingleBlockShuffle TriangularForms TriangularPermutation
  UnitalFamily UnitalProduct.
