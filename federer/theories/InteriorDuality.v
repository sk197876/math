(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Federer 1.5.2: both interior products on dual Grassmann bases,
    their complementary indices and signs, and the two duality
    isomorphisms D_p and D^p with inverse and product laws. *)
From Federer Require Export InteriorMultiplication.
From Federer Require Export InteriorComplements InteriorIndexRelations
  OrderedBasisWords CrossingCounts CovectorWords InteriorSigns
  CovectorBasisSeparation InteriorBasisEvaluation InteriorBasisFormula
  TopComplements DualityMaps DualityBasis DualityInverse
  DualityIsomorphism DualityProductLaws.
