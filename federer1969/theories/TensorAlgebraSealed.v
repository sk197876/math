(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlgebraUP GradedAlgebra TensorAlgebraUP.
Require Federer.WordTensorAlgebra Federer.WordTensorGrading Federer.WordTensorWitness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The tensor algebra used in the sequel (Federer 1.2.3). The signature
    exposes only the graded algebra, the generating map and the property
    [is_graded_tensor_algebra]; the opaque ascription hides the construction. *)
Module Type TensorAlgebraSig.
(** Source for [tensor_algebra]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_algebra : forall (K : fieldType) (V : lmodType K), algebra K.
(** Source for [tensor_generator_map]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_generator_map :
  forall (K : fieldType) (V : lmodType K), {linear V -> tensor_algebra V}.
(** Source for [tensor_grading]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_grading :
  forall (K : fieldType) (V : lmodType K), grading (tensor_algebra V).
(** Source for [tensor_algebraP]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_algebraP :
  forall (K : fieldType) (V : lmodType K),
  is_graded_tensor_algebra (tensor_generator_map V) (tensor_grading V).
End TensorAlgebraSig.

Module TensorAlgebraImpl <: TensorAlgebraSig.
(** Source for [tensor_algebra]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_algebra (K : fieldType) (V : lmodType K) : algebra K :=
  WordTensorAlgebra.tensor_algebra V.
(** Source for [tensor_generator_map]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_generator_map (K : fieldType) (V : lmodType K) :
    {linear V -> tensor_algebra V} :=
  WordTensorWitness.word_generator V.
(** Source for [tensor_grading]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_grading (K : fieldType) (V : lmodType K) :
    grading (tensor_algebra V) :=
  WordTensorGrading.tensor_grading V.
(** Source for [tensor_algebraP]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_algebraP (K : fieldType) (V : lmodType K) :
    is_graded_tensor_algebra (tensor_generator_map V) (tensor_grading V) :=
  WordTensorWitness.word_tensor_algebra_exists V.
End TensorAlgebraImpl.

Module TensorAlgebraSealed : TensorAlgebraSig := TensorAlgebraImpl.
Export TensorAlgebraSealed.
Arguments tensor_algebra {K} V.
Arguments tensor_generator_map {K} V.
Arguments tensor_grading {K} V.
Arguments tensor_algebraP {K} V.
