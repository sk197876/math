(** Federer (1969), 1.9.1, p. 41: private tensor-quotient construction of
    the symmetric algebra. This file proves existence; subsequent
    mathematics uses the sealed abstract interface. Arbitrary fields replace
    the sources' real scalars. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg generic_quotient.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP
  WordAlgebra TensorAlgebra AlgebraQuotient SymmetricUP SymmetricIdeal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricAlgebra.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation pi := (quotient_projection (commutator_ideal V)).

(** Source for [symmetric_space]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The vector space underlying the symmetric
    algebra. *)
Definition symmetric_space := quotient_algebra_space (commutator_ideal V).
HB.instance Definition _ := GRing.Lmodule.copy symmetric_space
  (quotient_algebra_space (commutator_ideal V)).

(** Source for [symmetric_algebra]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The commutative associative unital symmetric
    algebra. *)
Definition symmetric_algebra := quotient_algebra (commutator_ideal V).

(** Source for [symmetric_projection]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The canonical algebra map from the tensor
    algebra to the symmetric algebra. *)
Definition symmetric_projection := quotient_algebra_projection (commutator_ideal V).

(** Source for [symmetric_product]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Multiplication of symmetric products. *)
Definition symmetric_product : symmetric_space -> symmetric_space -> symmetric_space :=
  @quotient_mul K (tensor_algebra V) (commutator_ideal V).

(** Source for [symmetric_unit]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The unit, represented by the empty product. *)
Definition symmetric_unit : symmetric_space := quotient_one (commutator_ideal V).

(** Source for [symmetric_word]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The product of a finite sequence of
    generators; the empty sequence gives the unit. *)
Definition symmetric_word s : symmetric_space := pi (tensor_word s).

(** Source for [symmetric_generator]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: A vector regarded as a degree-one symmetric
    product. *)
Definition symmetric_generator v := symmetric_word [:: v].

(** Source for [symmetric_generator_linear]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Insertion of vectors into the algebra is
    linear. *)
Lemma symmetric_generator_linear : linear symmetric_generator.
Proof.
move=> a v w; change (pi (tensor_generator (a *: v + w)) =
  a *: pi (tensor_generator v) + pi (tensor_generator w)).
by rewrite !linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V symmetric_space
  *:%R symmetric_generator symmetric_generator_linear.

(** Source for [symmetric_product_bilinear]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Symmetric multiplication is bilinear. *)
Lemma symmetric_product_bilinear : bilinear symmetric_product.
Proof. exact: quotient_mul_bilinear. Qed.

(** Source for [symmetric_product_assoc]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Symmetric multiplication is associative. *)
Lemma symmetric_product_assoc : associative symmetric_product.
Proof. exact: quotient_mul_assoc. Qed.

(** Source for [symmetric_product_unitl]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The empty product is a left unit. *)
Lemma symmetric_product_unitl : left_id symmetric_unit symmetric_product.
Proof. exact: quotient_mul_unitl. Qed.

(** Source for [symmetric_product_unitr]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The empty product is a right unit. *)
Lemma symmetric_product_unitr : right_id symmetric_unit symmetric_product.
Proof. exact: quotient_mul_unitr. Qed.

(** Source for [symmetric_product_projection]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: The tensor projection preserves
    multiplication. *)
Lemma symmetric_product_projection x y : symmetric_product (pi x) (pi y) = pi (tensor_product x y).
Proof. exact: quotient_mulE. Qed.

(** Source for [symmetric_word_cat]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Multiplying two words concatenates their
    sequences of factors. *)
Lemma symmetric_word_cat s t :
  symmetric_product (symmetric_word s) (symmetric_word t) = symmetric_word (s ++ t).
Proof. by rewrite /symmetric_word symmetric_product_projection tensor_product_words. Qed.

(** Source for [symmetric_word_nil]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The empty word equals the algebra unit. *)
Lemma symmetric_word_nil : symmetric_word [::] = symmetric_unit.
Proof. by []. Qed.

(** Source for [symmetric_word_cons]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: A nonempty word is its first generator
    multiplied by the remaining word. *)
Lemma symmetric_word_cons v s :
  symmetric_word (v :: s) = symmetric_product (symmetric_generator v) (symmetric_word s).
Proof. exact: esym (symmetric_word_cat [:: v] s). Qed.

(** Source for [symmetric_word_induction]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Every element is a linear combination of
    words, yielding induction by words. *)
Lemma symmetric_word_induction (P : symmetric_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, P (symmetric_word s)) : forall x, P x.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective.
elim/tensor_word_induction: (repr x) => [|u v hu hv|a u hu|s].
- by rewrite linear0.
- rewrite linearD; exact: hD hu hv.
- rewrite linearZ; exact: hZ hu.
exact: hw.
Qed.

(** Source for [symmetric_algebra_induction]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: The unit and generators
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

(** Source for [symmetric_generator_commute]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: Two generators commute because
    their commutator vanishes in the quotient. *)
Lemma symmetric_generator_commute v w :
  symmetric_product (symmetric_generator v) (symmetric_generator w) =
  symmetric_product (symmetric_generator w) (symmetric_generator v).
Proof.
rewrite /symmetric_generator /symmetric_word !symmetric_product_projection.
apply/quotient_projection_eq; exact: commutator_ideal_generator.
Qed.

(** Source for [symmetric_generator_word_commute]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: A generator commutes with any
    word in the generators. *)
Lemma symmetric_generator_word_commute v s :
  symmetric_product (symmetric_generator v) (symmetric_word s) =
  symmetric_product (symmetric_word s) (symmetric_generator v).
Proof.
elim: s => [|w s ih].
- by rewrite symmetric_word_nil symmetric_product_unitl symmetric_product_unitr.
rewrite symmetric_word_cons symmetric_product_assoc symmetric_generator_commute
  -symmetric_product_assoc ih symmetric_product_assoc.
by [].
Qed.

(** Source for [symmetric_product_commute]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: Any two elements of the symmetric algebra
    commute. *)
Lemma symmetric_product_commute : commutative symmetric_product.
Proof.
move=> x y.
elim/symmetric_word_induction: x => [|x x' hx hx'|a x hx|s].
- by rewrite (bil0l symmetric_product_bilinear) (bil0r symmetric_product_bilinear).
- by rewrite (bilDl symmetric_product_bilinear) (bilDr symmetric_product_bilinear) hx hx'.
- by rewrite (bilZl symmetric_product_bilinear) (bilZr symmetric_product_bilinear) hx.
elim/symmetric_word_induction: y => [|y y' hy hy'|a y hy|t].
- by rewrite (bil0l symmetric_product_bilinear) (bil0r symmetric_product_bilinear).
- by rewrite (bilDl symmetric_product_bilinear) (bilDr symmetric_product_bilinear) hy hy'.
- by rewrite (bilZl symmetric_product_bilinear) (bilZr symmetric_product_bilinear) hy.
elim: s => [|v s ih].
- by rewrite symmetric_word_nil symmetric_product_unitl symmetric_product_unitr.
by rewrite symmetric_word_cons -symmetric_product_assoc ih
  symmetric_product_assoc symmetric_generator_word_commute -symmetric_product_assoc.
Qed.

Section Extension.
Variable A : algebra K.
Variable f : {linear V -> A}.
Hypothesis hc : commutative (alg_mul A).

(** Source for [symmetric_relation_killed]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The tensor extension to a commutative target
    kills the entire commutator ideal. *)
Lemma symmetric_relation_killed x : commutator_ideal V x -> tensor_algebra_extension f x = 0.
Proof.
elim=> [|u v hu ihu hv ihv|a u hu ihu|s t v w].
- exact: linear0.
- rewrite linearD; change (tensor_algebra_extension f u + tensor_algebra_extension f v = 0).
  by rewrite ihu ihv add0r.
- rewrite linearZ; change (a *: tensor_algebra_extension f u = 0).
  by rewrite ihu scaler0.
rewrite linearB !tensor_algebra_extension_word !word_eval_cat /=.
apply/eqP; rewrite subr_eq0; apply/eqP.
congr (alg_mul A (word_eval f s) _).
by rewrite !alg_assoc [alg_mul A (f v) (f w)]hc.
Qed.

(** Source for [symmetric_algebra_extension]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: The unique unit-preserving
    extension of a generator map to a commutative target. *)
Definition symmetric_algebra_extension : algebra_map symmetric_algebra A :=
  quotient_algebra_lift symmetric_relation_killed.

(** Source for [symmetric_algebra_extension_projection]: Federer 1.9.1, p.
    41, quotient, commutativity and universal-property paragraphs.
    Supporting construction for this passage, in words: Composing the
    symmetric extension with tensor projection recovers the tensor
    extension. *)
Lemma symmetric_algebra_extension_projection x :
  symmetric_algebra_extension (pi x) = tensor_algebra_extension f x.
Proof. exact: quotient_algebra_liftE. Qed.

(** Source for [symmetric_algebra_extension_word]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: The extension sends a word to
    the product of the images of its factors. *)
Lemma symmetric_algebra_extension_word s :
  symmetric_algebra_extension (symmetric_word s) = word_eval f s.
Proof.
by rewrite /symmetric_word symmetric_algebra_extension_projection tensor_algebra_extension_word.
Qed.

(** Source for [symmetric_algebra_extension_generator]: Federer 1.9.1, p.
    41, quotient, commutativity and universal-property paragraphs.
    Supporting construction for this passage, in words: The extension agrees
    with the original linear map on generators. *)
Lemma symmetric_algebra_extension_generator v :
  symmetric_algebra_extension (symmetric_generator v) = f v.
Proof.
by rewrite /symmetric_generator symmetric_algebra_extension_word /= alg_unitr.
Qed.

(** Source for [symmetric_algebra_extension_unique]: Federer 1.9.1, p. 41,
    quotient, commutativity and universal-property paragraphs. Supporting
    construction for this passage, in words: Any algebra homomorphism with
    the prescribed generator images equals the extension. *)
Lemma symmetric_algebra_extension_unique (g : algebra_map symmetric_algebra A) :
  (forall v, g (symmetric_generator v) = f v) ->
  forall x, g x = symmetric_algebra_extension x.
Proof.
move=> e x; rewrite -[x]quotient_projection_surjective symmetric_algebra_extension_projection.
have h : forall v, algebra_comp g symmetric_projection (tensor_generator v) = f v.
  exact: e.
exact: (tensor_algebra_extension_unique h).
Qed.
End Extension.

(** Source for [symmetric_algebra_exists]: Federer 1.9.1, p. 41, quotient,
    commutativity and universal-property paragraphs. Supporting construction
    for this passage, in words: The algebra satisfies the ungraded
    commutative-target universal property, strengthening the printed graded
    property. *)
Theorem symmetric_algebra_exists :
  @is_symmetric_algebra K V symmetric_algebra
    (GRing.Linear.clone _ _ _ _ symmetric_generator _).
Proof.
move=> A hf f; exists (symmetric_algebra_extension f hf); split.
  exact: symmetric_algebra_extension_generator.
exact: symmetric_algebra_extension_unique.
Qed.
End SymmetricAlgebra.
