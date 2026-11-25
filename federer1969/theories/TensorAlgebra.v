(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra WordEvaluation
  TensorAlgebraUP.
From Federer Require Export WordEvaluation TensorAlgebraSealed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3: the tensor algebra of V, words, products and the
    extension of linear maps. Everything follows from the property
    [is_graded_tensor_algebra] of the sealed tensor algebra. *)
Section TensorAlgebra.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation iota := (tensor_generator_map V).

(** Source for [tensor_algebra_space]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_algebra_space : lmodType K := tensor_algebra V.

(** Source for [tensor_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_word (s : seq V) : tensor_algebra_space := word_eval iota s.
(** Source for [tensor_unit]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_unit := tensor_word [::].
(** Source for [tensor_generator]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_generator (v : V) := tensor_word [:: v].

(** Source for [tensor_generator_mapE]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generator_mapE v : iota v = tensor_generator v.
Proof. by rewrite /tensor_generator /tensor_word /= alg_unitr. Qed.

(** Source for [tensor_generatorD]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generatorD v w :
  tensor_generator (v + w) = tensor_generator v + tensor_generator w.
Proof. by rewrite -!tensor_generator_mapE linearD. Qed.
(** Source for [tensor_generatorZ]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generatorZ a v : tensor_generator (a *: v) = a *: tensor_generator v.
Proof. by rewrite -!tensor_generator_mapE linearZ. Qed.
(** Source for [tensor_generator_linear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generator_linear : linear tensor_generator.
Proof. by move=> a v w; rewrite tensor_generatorD tensor_generatorZ. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V tensor_algebra_space
  *:%R tensor_generator tensor_generator_linear.

(** Source for [tensor_product]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_product (x y : tensor_algebra_space) : tensor_algebra_space :=
  alg_mul (tensor_algebra V) x y.

(** Source for [tensor_product_words]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_product_words s t : tensor_product (tensor_word s) (tensor_word t) =
  tensor_word (s ++ t).
Proof. by rewrite /tensor_product /tensor_word word_eval_cat. Qed.

(** Source for [tensor_product_bilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_product_bilinear : bilinear tensor_product.
Proof. exact: alg_bilinear. Qed.
(** Source for [tensor_product_assoc]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_assoc : associative tensor_product.
Proof. exact: alg_assoc. Qed.
(** Source for [tensor_product_unitl]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_unitl : left_id tensor_unit tensor_product.
Proof. exact: alg_unitl. Qed.
(** Source for [tensor_product_unitr]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_unitr : right_id tensor_unit tensor_product.
Proof. exact: alg_unitr. Qed.

(** Source for [tensor_word_induction]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_word_induction (P : tensor_algebra_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, P (tensor_word s)) : forall x, P x.
Proof. exact: (word_induction (tensor_algebraP V) h0 hD hZ hw). Qed.

Section Extension.
Variable A : algebra K.
Variable f : {linear V -> A}.

(** Source for [tensor_algebra_extension]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Definition or construction used to formalise this passage. The ungraded
    universal property is a local strengthening; it is not the literal
    graded property stated in this passage. *)
Definition tensor_algebra_extension : algebra_map (tensor_algebra V) A :=
  graded_extension (tensor_algebraP V) f.

(** Source for [tensor_algebra_extension_word]: Federer (1969), 1.2.3, p.
    12, graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma tensor_algebra_extension_word s :
  tensor_algebra_extension (tensor_word s) = word_eval f s.
Proof. exact: graded_extension_word. Qed.

(** Source for [tensor_algebra_extension_generator]: Federer (1969), 1.2.3,
    p. 12, graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma tensor_algebra_extension_generator v :
  tensor_algebra_extension (tensor_generator v) = f v.
Proof. by rewrite tensor_algebra_extension_word /= alg_unitr. Qed.

(** Source for [tensor_algebra_extension_unique]: Federer (1969), 1.2.3, p.
    12, graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. The ungraded universal property is a local
    strengthening; it is not the literal graded property stated in this
    passage. *)
Lemma tensor_algebra_extension_unique (g : algebra_map (tensor_algebra V) A) :
  (forall v, g (tensor_generator v) = f v) ->
  forall x, g x = tensor_algebra_extension x.
Proof.
move=> hg; apply: graded_extension_unique => v.
by rewrite tensor_generator_mapE hg.
Qed.
End Extension.

(** Source for [tensor_algebra_exists]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The ungraded universal property is a local strengthening; it is
    not the literal graded property stated in this passage. *)
Theorem tensor_algebra_exists :
  @is_tensor_algebra K V (tensor_algebra V)
    (GRing.Linear.clone _ _ _ _ tensor_generator _).
Proof.
move=> B f; exists (tensor_algebra_extension f); split.
  exact: tensor_algebra_extension_generator.
exact: tensor_algebra_extension_unique.
Qed.
End TensorAlgebra.
