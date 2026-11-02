(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Public entry point through Federer 1.4.1. The numbered coverage
    record is in docs/chapter1.md. Each claim has a source comment. *)
From Federer Require Export Exterior Hom HomogeneousHom
  AlternatingForms AlternatingWords AlternatingExtension AlternatingZero
  AlternatingIsomorphism BoundedHom HomogeneousSum HomFiniteFunctor
  AlternatingSum AlternatingPairing AlternatingDual.
