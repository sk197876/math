(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlgebraUP GradedAlgebra ExteriorAlgebraUP.
Require Federer.ExteriorQuotient Federer.ExteriorQuotientGrading
  Federer.ExteriorQuotientWitness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exterior algebra used in the sequel (Federer 1.3.1). The signature
    exposes only the graded algebra, the generating map and the property
    [is_exterior_power_algebra]; the opaque ascription hides the quotient
    construction. *)
Module Type ExteriorAlgebraSig.
(** Source for [exterior_algebra]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Sealed interface specification for this passage; the implementation
    proves this obligation. *)
Parameter exterior_algebra : forall (K : fieldType) (V : lmodType K), algebra K.
(** Source for [exterior_generator_map]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Sealed interface specification for this passage; the
    implementation proves this obligation. *)
Parameter exterior_generator_map :
  forall (K : fieldType) (V : lmodType K), {linear V -> exterior_algebra V}.
(** Source for [exterior_grading]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Sealed interface specification for this passage; the implementation
    proves this obligation. *)
Parameter exterior_grading :
  forall (K : fieldType) (V : lmodType K), grading (exterior_algebra V).
(** Source for [exterior_algebraP]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Sealed interface specification for this passage; the implementation
    proves this obligation. *)
Parameter exterior_algebraP :
  forall (K : fieldType) (V : lmodType K),
  is_exterior_power_algebra (exterior_generator_map V) (exterior_grading V).
End ExteriorAlgebraSig.

Module ExteriorAlgebraImpl <: ExteriorAlgebraSig.
(** Source for [exterior_algebra]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_algebra (K : fieldType) (V : lmodType K) : algebra K :=
  ExteriorQuotient.exterior_algebra V.
(** Source for [exterior_generator_map]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_generator_map (K : fieldType) (V : lmodType K) :
    {linear V -> exterior_algebra V} :=
  ExteriorQuotientWitness.exterior_quotient_generator V.
(** Source for [exterior_grading]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_grading (K : fieldType) (V : lmodType K) :
    grading (exterior_algebra V) :=
  ExteriorQuotientGrading.exterior_grading V.
(** Source for [exterior_algebraP]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_algebraP (K : fieldType) (V : lmodType K) :
    is_exterior_power_algebra (exterior_generator_map V) (exterior_grading V) :=
  ExteriorQuotientWitness.exterior_quotient_exists V.
End ExteriorAlgebraImpl.

Module ExteriorAlgebraSealed : ExteriorAlgebraSig := ExteriorAlgebraImpl.
Export ExteriorAlgebraSealed.
Arguments exterior_algebra {K} V.
Arguments exterior_generator_map {K} V.
Arguments exterior_grading {K} V.
Arguments exterior_algebraP {K} V.
