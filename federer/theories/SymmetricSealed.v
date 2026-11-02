(** Federer (1969), 1.9.1, p. 41: the symmetric algebra exposed by its
    graded power universal property. Opaque module ascription hides the
    proved tensor-quotient existence construction. The interface works over
    arbitrary fields. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlgebraUP GradedAlgebra SymmetricAlgebraUP.
Require Federer.SymmetricQuotient Federer.SymmetricQuotientGrading
  Federer.SymmetricQuotientWitness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SymmetricAlgebraSig.

(** Source for [symmetric_algebra]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The commutative associative unital algebra of symmetric
    products, specified independently of the construction.
    This sealed interface obligation is proved by the implementation. *)
Parameter symmetric_algebra : forall (K : fieldType) (V : lmodType K), algebra K.

(** Source for [symmetric_generator_map]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The linear insertion of vectors as degree-one generators.
    This sealed interface obligation is proved by the implementation. *)
Parameter symmetric_generator_map :
  forall (K : fieldType) (V : lmodType K), {linear V -> symmetric_algebra V}.

(** Source for [symmetric_grading]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The homogeneous grading, including degrees zero and one.
    This sealed interface obligation is proved by the implementation. *)
Parameter symmetric_grading :
  forall (K : fieldType) (V : lmodType K), grading (symmetric_algebra V).

(** Source for [symmetric_algebraP]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The symmetric-multilinear universal properties of all
    homogeneous powers, together with commutativity and homogeneous words.
    This sealed interface obligation is proved by the implementation. *)
Parameter symmetric_algebraP :
  forall (K : fieldType) (V : lmodType K),
  is_symmetric_power_algebra (symmetric_generator_map V) (symmetric_grading V).
End SymmetricAlgebraSig.

Module SymmetricAlgebraImpl <: SymmetricAlgebraSig.

(** Source for [symmetric_algebra]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The commutative associative unital algebra of symmetric
    products, specified independently of the construction.
    This sealed interface obligation is proved by the implementation. *)
Definition symmetric_algebra (K : fieldType) (V : lmodType K) : algebra K :=
  SymmetricQuotient.symmetric_algebra V.

(** Source for [symmetric_generator_map]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The linear insertion of vectors as degree-one generators.
    This sealed interface obligation is proved by the implementation. *)
Definition symmetric_generator_map (K : fieldType) (V : lmodType K) :
    {linear V -> symmetric_algebra V} :=
  SymmetricQuotientWitness.symmetric_quotient_generator V.

(** Source for [symmetric_grading]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The homogeneous grading, including degrees zero and one.
    This sealed interface obligation is proved by the implementation. *)
Definition symmetric_grading (K : fieldType) (V : lmodType K) :
    grading (symmetric_algebra V) :=
  SymmetricQuotientGrading.symmetric_grading V.

(** Source for [symmetric_algebraP]: Federer 1.9.1, p. 41,
    quotient, homogeneous-powers and universal-property paragraphs.
    The symmetric-multilinear universal properties of all
    homogeneous powers, together with commutativity and homogeneous words.
    This sealed interface obligation is proved by the implementation. *)
Definition symmetric_algebraP (K : fieldType) (V : lmodType K) :
    is_symmetric_power_algebra (symmetric_generator_map V) (symmetric_grading V) :=
  SymmetricQuotientWitness.symmetric_quotient_exists V.
End SymmetricAlgebraImpl.

Module SymmetricAlgebraSealed : SymmetricAlgebraSig := SymmetricAlgebraImpl.
Export SymmetricAlgebraSealed.
Arguments symmetric_algebra {K} V.
Arguments symmetric_generator_map {K} V.
Arguments symmetric_grading {K} V.
Arguments symmetric_algebraP {K} V.
