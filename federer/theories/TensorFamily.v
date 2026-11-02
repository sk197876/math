(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Public entry point for the tensor product of V_1, …, V_m (Federer 1.1.1).
    It exports the universal property and the sealed tensor products, not
    the construction. *)
From Federer Require Export FamilyUpdate TensorFamilyUP TensorFamilySpan
  TensorFamilyBinary TensorSealed.
