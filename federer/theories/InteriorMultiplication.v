(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. This file only exports or audits claims; imported
    declarations carry precise locators. *)

(** Federer 1.5.1: the two interior multiplications, their independent
    characteristic conditions, constructions, uniqueness, bilinearity,
    the displayed commutative diagram and both final identities. *)
From Federer Require Export GrassmannTrace.
From Federer Require Export ExteriorHomogeneousProducts InteriorUP
  PairingSeparation ScalarTensorContraction RightInteriorHom RightInterior
  RightInteriorLaws LeftInteriorHom LeftInteriorDegree LeftInterior
  InteriorAssociativity.
