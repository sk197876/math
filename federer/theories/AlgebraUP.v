(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Associativity and a unit are additional data, not part of the definition
    of a graded algebra in Federer 1.2.1. This structure is used in 1.2.3. *)
(** Source for [algebra]: Federer (1969), 1.2.1, p. 11, paragraph beginning
    Usually. In words: Associativity and a scalar identification of degree
    zero taking one to the unit are usual additional conditions, not part of
    the preceding general definition. Definition or construction used to
    formalise this passage. *)
Record algebra (K : fieldType) := Algebra {
  alg_space :> lmodType K;
  alg_mul : alg_space -> alg_space -> alg_space;
  alg_one : alg_space;
  alg_bilinear : bilinear alg_mul;
  alg_assoc : associative alg_mul;
  alg_unitl : left_id alg_one alg_mul;
  alg_unitr : right_id alg_one alg_mul
}.
Arguments alg_mul {K} a _ _.
Arguments alg_one {K} a.

Section AlgebraMaps.
Variable K : fieldType.
Variables A B C : algebra K.

(** Source for [algebra_map]: Federer (1969), 1.2.3, p. 12, universal
    mapping property in the last two paragraphs. In words: Every linear map
    into the degree-one part of a unital associative graded algebra extends
    uniquely to a unit-preserving graded algebra homomorphism. Definition or
    construction used to formalise this passage. *)
Record algebra_map := AlgebraMap {
  algebra_map_linear :> {linear A -> B};
  algebra_map_one : algebra_map_linear (alg_one A) = alg_one B;
  algebra_map_mul : forall x y,
    algebra_map_linear (alg_mul A x y) =
    alg_mul B (algebra_map_linear x) (algebra_map_linear y)
}.
End AlgebraMaps.

Section AlgebraComposition.
Variable K : fieldType.
Variables A B C : algebra K.

(** Source for [algebra_id]: Federer (1969), 1.2.3, p. 12, universal mapping
    property in the last two paragraphs. In words: Every linear map into the
    degree-one part of a unital associative graded algebra extends uniquely
    to a unit-preserving graded algebra homomorphism. Definition or
    construction used to formalise this passage. *)
Definition algebra_id : algebra_map A A.
Proof. apply: (@AlgebraMap K A A (linear_id A)); by []. Defined.

(** Source for [algebra_comp]: Federer (1969), 1.2.3, p. 12, universal
    mapping property in the last two paragraphs. In words: Every linear map
    into the degree-one part of a unital associative graded algebra extends
    uniquely to a unit-preserving graded algebra homomorphism. Definition or
    construction used to formalise this passage. *)
Definition algebra_comp (f : algebra_map B C) (g : algebra_map A B) : algebra_map A C.
Proof.
apply: (@AlgebraMap K A C (linear_comp f g)).
  by rewrite /= !algebra_map_one.
by move=> x y /=; rewrite !algebra_map_mul.
Defined.
End AlgebraComposition.

(** Construction-independent universal property of the tensor algebra. *)
Section UniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.

(** Source for [is_tensor_algebra]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Definition or
    construction used to formalise this passage. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Definition is_tensor_algebra : Prop :=
  forall (B : algebra K) (f : {linear V -> B}),
  exists g : algebra_map A B,
    (forall v, g (iota v) = f v) /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = f v) -> forall x, h x = g x).

(** Source for [tensor_algebra_ext]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Supporting lemma for
    this passage; not separately stated in the book. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Lemma tensor_algebra_ext (H : is_tensor_algebra) (B : algebra K)
    (f g : algebra_map A B) :
  (forall v, f (iota v) = g (iota v)) -> forall x, f x = g x.
Proof.
move=> e.
have [h [hi hu]] := H B (linear_comp g iota).
by move=> x; rewrite (hu f e) (hu g (fun v => erefl _)).
Qed.
End UniversalProperty.
Arguments tensor_algebra_ext {K V A iota} H {B} f g _ x.

Section Uniqueness.
Variable K : fieldType.
Variable V : lmodType K.
Variables A B : algebra K.
Variables (iota : {linear V -> A}) (iota' : {linear V -> B}).
Hypotheses (H : is_tensor_algebra iota) (H' : is_tensor_algebra iota').

(** Source for [tensor_algebra_unique]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The ungraded universal property is a local strengthening; it is
    not the literal graded property stated in this passage. *)
Theorem tensor_algebra_unique :
  exists (f : algebra_map A B) (g : algebra_map B A),
    (forall v, f (iota v) = iota' v) /\
    (forall v, g (iota' v) = iota v) /\
    cancel f g /\ cancel g f /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = iota' v) -> forall x, h x = f x).
Proof.
have [f [fi fu]] := H iota'.
have [g [gi gu]] := H' iota.
exists f, g; split=> //; split=> //; split.
  apply: (tensor_algebra_ext H (algebra_comp g f) (algebra_id A)) => v /=.
  by rewrite fi gi.
split.
  apply: (tensor_algebra_ext H' (algebra_comp f g) (algebra_id B)) => v /=.
  by rewrite gi fi.
exact: fu.
Qed.
End Uniqueness.
