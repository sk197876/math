(** Federer (1969), 1.9.1, pp. 41-42: public symmetric algebra. Every law
    below follows from the sealed universal property; the private commutator
    quotient is not imported or unfolded here. Arbitrary fields replace the
    sources' real scalars. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra
  TensorAlgebra CommutativeWords SymmetricUP SymmetricAlgebraUP.
From Federer Require Export WordEvaluation SymmetricSealed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricAlgebra.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation iota := (symmetric_generator_map V).
Local Notation H := (symmetric_algebraP V).

(** Source for [symmetric_space]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The vector space underlying the
    symmetric algebra. *)
Definition symmetric_space : lmodType K := symmetric_algebra V.

(** Source for [symmetric_product]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Multiplication of symmetric
    products. *)
Definition symmetric_product (x y : symmetric_space) : symmetric_space :=
  alg_mul (symmetric_algebra V) x y.

(** Source for [symmetric_unit]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The unit, represented by the empty
    product. *)
Definition symmetric_unit : symmetric_space := alg_one (symmetric_algebra V).

(** Source for [symmetric_word]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The product of a finite sequence of
    generators; the empty sequence gives the unit. *)
Definition symmetric_word (s : seq V) : symmetric_space := word_eval iota s.

(** Source for [symmetric_generator]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: A vector regarded as a degree-one
    symmetric product. *)
Definition symmetric_generator (v : V) := symmetric_word [:: v].

(** Source for [symmetric_generator_mapE]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The one-letter word agrees with the
    generating linear map. *)
Lemma symmetric_generator_mapE v : iota v = symmetric_generator v.
Proof. by rewrite /symmetric_generator /symmetric_word /= alg_unitr. Qed.

(** Source for [symmetric_generator_linear]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Insertion of vectors into the
    algebra is linear. *)
Lemma symmetric_generator_linear : linear symmetric_generator.
Proof. by move=> a v w; rewrite -!symmetric_generator_mapE linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V symmetric_space
  *:%R symmetric_generator symmetric_generator_linear.

(** Source for [symmetric_product_bilinear]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Symmetric multiplication is
    bilinear. *)
Lemma symmetric_product_bilinear : bilinear symmetric_product.
Proof. exact: alg_bilinear. Qed.

(** Source for [symmetric_product_assoc]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Symmetric multiplication is
    associative. *)
Lemma symmetric_product_assoc : associative symmetric_product.
Proof. exact: alg_assoc. Qed.

(** Source for [symmetric_product_unitl]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The empty product is a left unit. *)
Lemma symmetric_product_unitl : left_id symmetric_unit symmetric_product.
Proof. exact: alg_unitl. Qed.

(** Source for [symmetric_product_unitr]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The empty product is a right unit. *)
Lemma symmetric_product_unitr : right_id symmetric_unit symmetric_product.
Proof. exact: alg_unitr. Qed.

(** Source for [symmetric_word_cat]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Multiplying two words concatenates
    their sequences of factors. *)
Lemma symmetric_word_cat s t :
  symmetric_product (symmetric_word s) (symmetric_word t) = symmetric_word (s ++ t).
Proof. by rewrite /symmetric_product /symmetric_word word_eval_cat. Qed.

(** Source for [symmetric_word_nil]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The empty word equals the algebra
    unit. *)
Lemma symmetric_word_nil : symmetric_word [::] = symmetric_unit.
Proof. by []. Qed.

(** Source for [symmetric_word_cons]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: A nonempty word is its first
    generator multiplied by the remaining word. *)
Lemma symmetric_word_cons v s :
  symmetric_word (v :: s) = symmetric_product (symmetric_generator v) (symmetric_word s).
Proof. exact: esym (symmetric_word_cat [:: v] s). Qed.

(** Source for [symmetric_word_induction]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Every element is a linear
    combination of words, yielding induction by words. *)
Lemma symmetric_word_induction (P : symmetric_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, P (symmetric_word s)) : forall x, P x.
Proof. exact: (sym_word_induction H h0 hD hZ hw). Qed.

(** Source for [symmetric_algebra_induction]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    definition or lemma for this passage, in words: The unit and generators
    generate the algebra under addition, scaling, and multiplication. *)
Lemma symmetric_algebra_induction (P : symmetric_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (h1 : P symmetric_unit) (hV : forall v, P (symmetric_generator v))
    (hm : forall x y, P x -> P y -> P (symmetric_product x y)) : forall x, P x.
Proof.
apply: symmetric_word_induction => // s.
elim: s => [|v s ih]; first exact: h1.
rewrite symmetric_word_cons; exact: hm (hV v) ih.
Qed.

(** Source for [symmetric_product_commute]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Any two elements of the symmetric
    algebra commute. *)
Lemma symmetric_product_commute : commutative symmetric_product.
Proof. exact: symmetric_commutative H. Qed.

(** Source for [symmetric_word_permutation]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: A finite product of generators is
    invariant under permutation of its factors. *)
Lemma symmetric_word_permutation s t : perm_eq s t -> symmetric_word s = symmetric_word t.
Proof. exact (@commutative_word_permutation K V (symmetric_algebra V)
  (symmetric_commutative H) iota s t). Qed.

(** Source for [symmetric_projection]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The canonical algebra map from the
    tensor algebra to the symmetric algebra. *)
Definition symmetric_projection : algebra_map (tensor_algebra V) (symmetric_algebra V) :=
  tensor_algebra_extension iota.

(** Source for [symmetric_projection_word]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: Tensor projection sends a tensor
    word to the corresponding symmetric word. *)
Lemma symmetric_projection_word s : symmetric_projection (tensor_word s) = symmetric_word s.
Proof. exact: tensor_algebra_extension_word. Qed.

(** Source for [symmetric_product_projection]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    definition or lemma for this passage, in words: The tensor projection
    preserves multiplication. *)
Lemma symmetric_product_projection x y :
  symmetric_product (symmetric_projection x) (symmetric_projection y) =
  symmetric_projection (tensor_product x y).
Proof. by rewrite /symmetric_product -algebra_map_mul. Qed.

Section Extension.
Variable A : algebra K.
Variable f : {linear V -> A}.
Hypothesis hc : commutative (alg_mul A).

(** Source for [symmetric_algebra_extension]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    definition or lemma for this passage, in words: The unique
    unit-preserving extension of a generator map to a commutative target. *)
Definition symmetric_algebra_extension : algebra_map (symmetric_algebra V) A :=
  sym_extension H f hc.

(** Source for [symmetric_algebra_extension_word]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    definition or lemma for this passage, in words: The extension sends a
    word to the product of the images of its factors. *)
Lemma symmetric_algebra_extension_word s :
  symmetric_algebra_extension (symmetric_word s) = word_eval f s.
Proof. exact: sym_extension_word. Qed.

(** Source for [symmetric_algebra_extension_generator]: Federer 1.9.1, p.
    41, quotient, commutativity and universal-property paragraphs.
    Supporting definition or lemma for this passage, in words: The extension
    agrees with the original linear map on generators. *)
Lemma symmetric_algebra_extension_generator v :
  symmetric_algebra_extension (symmetric_generator v) = f v.
Proof. by rewrite symmetric_algebra_extension_word /= alg_unitr. Qed.

(** Source for [symmetric_algebra_extension_projection]: Federer 1.9.1, p.
    41, quotient, commutativity and universal-property paragraphs.
    Supporting definition or lemma for this passage, in words: Composing the
    symmetric extension with tensor projection recovers the tensor
    extension. *)
Lemma symmetric_algebra_extension_projection x :
  symmetric_algebra_extension (symmetric_projection x) = tensor_algebra_extension f x.
Proof.
have e : forall v, algebra_comp symmetric_algebra_extension symmetric_projection
    (tensor_generator v) = f v.
  move=> v; change (symmetric_algebra_extension (symmetric_projection (tensor_word [:: v]))
    = f v).
  by rewrite symmetric_projection_word symmetric_algebra_extension_word /= alg_unitr.
exact: (tensor_algebra_extension_unique e x).
Qed.

(** Source for [symmetric_algebra_extension_unique]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    definition or lemma for this passage, in words: Any algebra homomorphism
    with the prescribed generator images equals the extension. *)
Lemma symmetric_algebra_extension_unique (g : algebra_map (symmetric_algebra V) A) :
  (forall v, g (symmetric_generator v) = f v) ->
  forall x, g x = symmetric_algebra_extension x.
Proof.
move=> e; apply: sym_extension_unique => v.
by rewrite symmetric_generator_mapE e.
Qed.
End Extension.

(** Source for [symmetric_algebra_exists]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting definition
    or lemma for this passage, in words: The algebra satisfies the ungraded
    commutative-target universal property, strengthening the printed graded
    property. *)
Theorem symmetric_algebra_exists :
  @is_symmetric_algebra K V (symmetric_algebra V)
    (GRing.Linear.clone _ _ _ _ symmetric_generator _).
Proof.
move=> A hf f; exists (symmetric_algebra_extension f hf); split.
  exact: symmetric_algebra_extension_generator.
exact: symmetric_algebra_extension_unique.
Qed.
End SymmetricAlgebra.
Arguments symmetric_word {K V} s : simpl never.
