(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Federer 1.5.3: the auxiliary decomposition, its two annihilation
    conditions, the displayed covector identity, both equivalences, the
    direct sum and the final dual identity. Positive j is written n+1;
    the degree-zero auxiliary form is included explicitly. *)
From Federer Require Export InteriorDuality.
From Federer Require Export OneCovectorFactors RightPsiActions
  LeftCovectorContraction RightCovectorConvolution InteriorOneDegree
  InteriorNilpotency InteriorAuxiliaryDecomposition SubspaceSums
  InteriorConsequences InteriorDualDecomposition.
