(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, final parenthesis: the W-module structures on Hom(V,W)
    and A*(V,W) are pointwise multiplication by W. *)
Section CoefficientAction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Local Notation A := (alternating_unital_algebra h2 V W).
Local Notation E := (exterior_space V).
(** Source for [Hom_action]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition Hom_action w (a : Hom V W) : Hom V W :=
  hom_comp (hom_of_linear (algebra_left w)) a.
(** Source for [Hom_actionE]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma Hom_actionE w a v : Hom_action w a v = alg_mul W w (a v).
Proof. by []. Qed.
(** Source for [Hom_action_bilinear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Formalises the indicated part of the
    passage under the hypotheses in the statement below. The local LaTeX
    erratum, p. 1, entry for book p. 20 line 11, changes the printed wording
    to in case. *)
Lemma Hom_action_bilinear : bilinear Hom_action.
Proof.
split=> [a c w z|w c a b]; apply: hom_ext => v.
- by rewrite !Hom_actionE !hom_addE !hom_scaleE (proj1 (alg_bilinear W)).
- by rewrite !Hom_actionE !hom_addE !hom_scaleE (proj2 (alg_bilinear W)).
Qed.
(** Source for [Hom_action_unit]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Formalises the indicated part of the
    passage under the hypotheses in the statement below. The local LaTeX
    erratum, p. 1, entry for book p. 20 line 11, changes the printed wording
    to in case. *)
Lemma Hom_action_unit a : Hom_action (alg_one W) a = a.
Proof. apply: hom_ext => v; exact: alg_unitl. Qed.
(** Source for [Hom_action_assoc]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Formalises the indicated part of the
    passage under the hypotheses in the statement below. The local LaTeX
    erratum, p. 1, entry for book p. 20 line 11, changes the printed wording
    to in case. *)
Lemma Hom_action_assoc w z a : Hom_action w (Hom_action z a) = Hom_action (alg_mul W w z) a.
Proof. apply: hom_ext => v; exact: alg_assoc. Qed.
(** Source for [coefficient_product_left_tensor]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_product_left_tensor w (a : A) x :
  paired_tensor (alg_bilinear W) (coefficient_form V w) a x =
  alg_mul W w (a (counit_left V x)).
Proof.
apply: (tensor_ext (tensor_exists E E)
  (paired_tensor (alg_bilinear W) (coefficient_form V w) a)
  (linear_comp (algebra_left w) (linear_comp (hom_as_linear a) (counit_left V)))) x => u v.
change (paired_tensor (alg_bilinear W) (coefficient_form V w) a (tensor_inj u v) =
  alg_mul W w (a (counit_left V (tensor_inj u v)))).
by rewrite paired_tensorE coefficient_formE counit_leftE
  (linZ (hom_linear a)) (bilZl (alg_bilinear W)) (bilZr (alg_bilinear W)).
Qed.
(** Source for [coefficient_product_right_tensor]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_product_right_tensor w (a : A) x :
  paired_tensor (alg_bilinear W) a (coefficient_form V w) x =
  alg_mul W (a (counit_right V x)) w.
Proof.
apply: (tensor_ext (tensor_exists E E)
  (paired_tensor (alg_bilinear W) a (coefficient_form V w))
  (linear_comp (algebra_right w) (linear_comp (hom_as_linear a) (counit_right V)))) x => u v.
change (paired_tensor (alg_bilinear W) a (coefficient_form V w) (tensor_inj u v) =
  alg_mul W (a (counit_right V (tensor_inj u v))) w).
by rewrite paired_tensorE coefficient_formE counit_rightE
  (linZ (hom_linear a)) (bilZr (alg_bilinear W)) (bilZl (alg_bilinear W)).
Qed.
(** Source for [coefficient_product_leftE]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_product_leftE w (a : A) x :
  alg_mul A (coefficient_form V w) a x = alg_mul W w (a x).
Proof. by rewrite alternating_wedgeE coefficient_product_left_tensor counit_left_Psi. Qed.
(** Source for [coefficient_product_rightE]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_product_rightE w (a : A) x :
  alg_mul A a (coefficient_form V w) x = alg_mul W (a x) w.
Proof. by rewrite alternating_wedgeE coefficient_product_right_tensor counit_right_Psi. Qed.
(** Source for [coefficient_product]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_product w z :
  alg_mul A (coefficient_form V w) (coefficient_form V z) = coefficient_form V (alg_mul W w z).
Proof.
apply: hom_finite_ext => x.
by rewrite coefficient_product_leftE !coefficient_formE (bilZr (alg_bilinear W)).
Qed.
(** Source for [coefficient_algebra_map]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition coefficient_algebra_map : algebra_map W A :=
  @AlgebraMap K W A (GRing.Linear.clone _ _ _ _ (@coefficient_form K V W) _)
    (erefl _) (fun w z => esym (coefficient_product w z)).
(** Source for [coefficient_central]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_central (hc : commutative (alg_mul W)) w (a : A) :
  alg_mul A (coefficient_form V w) a = alg_mul A a (coefficient_form V w).
Proof. apply: hom_finite_ext => x; by rewrite coefficient_product_leftE coefficient_product_rightE hc. Qed.
(** Source for [one_generator_balance]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma one_generator_balance w a : one_generator (Hom_action w a) = alg_mul A (coefficient_form V w) (one_generator a).
Proof.
apply: hom_finite_ext; apply: exterior_word_induction => [|x y hx hy|c x hx|s].
- by rewrite !linear0.
- rewrite !linearD.
  change (one_generator (Hom_action w a) x + one_generator (Hom_action w a) y =
    alg_mul A (coefficient_form V w) (one_generator a) x + alg_mul A (coefficient_form V w) (one_generator a) y).
  by rewrite hx hy.
- rewrite !linearZ.
  change (c *: one_generator (Hom_action w a) x = c *: alg_mul A (coefficient_form V w) (one_generator a) x).
  by rewrite hx.
rewrite coefficient_product_leftE !one_generator_word.
case: s => [|v [|v' s]].
- by rewrite !form_words_wrong // (bil0r (alg_bilinear W)).
- change (form_words (one_form (Hom_action w a)) [tuple v] = alg_mul W w (form_words (one_form a) [tuple v])).
  by rewrite !form_wordsE !one_formE.
- by rewrite !form_words_wrong // (bil0r (alg_bilinear W)).
Qed.
End CoefficientAction.
