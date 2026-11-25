(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Core construction and maps for Federer 1.3.1. The numbered coverage record is in
    docs/chapter1.md. Source comments identify the paragraphs within 1.3.1. *)
From Federer Require Export Graded AlgebraQuotient GradedComponents
  ExteriorUP ExteriorIdeal ExteriorAlgebraUP ExteriorAlgebra ExteriorGrading
  ExteriorAnticommutativity ExteriorMaps ExteriorPowers.
