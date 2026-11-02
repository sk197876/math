(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification CoefficientAction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: change coefficients without changing degree. *)
Section CoefficientMap.
Variable K : fieldType.
Variables V W Z : lmodType K.
Variable f : {linear W -> Z}.
(** Source for [coefficient_map_bounded]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficient_map_bounded (a : A_star V W) :
  hom_finite_pred (exterior_grading V) (hom_comp (hom_of_linear f) a).
Proof.
apply/asboolP; have [N hN] := hom_finite_bound a; exists N => n x hn hx.
by rewrite hom_compE hom_of_linearE (hN n x hn hx) linear0.
Qed.
(** Source for [A_star_coefficients]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition A_star_coefficients (a : A_star V W) : A_star V Z :=
  @FiniteHom K (exterior_space V) Z (exterior_grading V)
    (hom_comp (hom_of_linear f) a) (coefficient_map_bounded a).
(** Source for [A_star_coefficientsE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma A_star_coefficientsE a x : A_star_coefficients a x = f (a x).
Proof. by []. Qed.
(** Source for [A_star_coefficients_linear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma A_star_coefficients_linear : linear A_star_coefficients.
Proof. move=> c a b; apply: hom_finite_ext => x; by rewrite !A_star_coefficientsE !hom_finite_addE !hom_finite_scaleE linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (A_star V W) (A_star V Z)
  *:%R A_star_coefficients A_star_coefficients_linear.
(** Source for [A_star_coefficients_constant]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma A_star_coefficients_constant w : A_star_coefficients (coefficient_form V w) = coefficient_form V (f w).
Proof. apply: hom_finite_ext => x; by rewrite A_star_coefficientsE !coefficient_formE linearZ. Qed.
(** Source for [A_star_coefficients_one]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma A_star_coefficients_one a : A_star_coefficients (one_generator a) =
  one_generator (hom_comp (hom_of_linear f) a).
Proof.
apply: hom_finite_ext; apply: exterior_word_induction => [|x y hx hy|c x hx|s].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : Z => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : Z => c *: x) hx).
rewrite A_star_coefficientsE !one_generator_word.
case: s => [|v [|v' s]].
- by rewrite !form_words_wrong // linear0.
- change (f (form_words (one_form a) [tuple v]) = form_words (one_form (hom_comp (hom_of_linear f) a)) [tuple v]).
  by rewrite !form_wordsE !one_formE.
- by rewrite !form_words_wrong // linear0.
Qed.
End CoefficientMap.

Section CoefficientAlgebraMap.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables W Z : algebra K.
Variable f : algebra_map W Z.
Local Notation A := (alternating_unital_algebra h2 V W).
Local Notation B := (alternating_unital_algebra h2 V Z).
(** Source for [coefficients_paired_tensor]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma coefficients_paired_tensor (a b : A) t :
  f (paired_tensor (alg_bilinear W) a b t) =
  paired_tensor (alg_bilinear Z) (A_star_coefficients f a) (A_star_coefficients f b) t.
Proof.
apply: (tensor_ext (tensor_exists (exterior_space V) (exterior_space V))
  (linear_comp f (paired_tensor (alg_bilinear W) a b))
  (paired_tensor (alg_bilinear Z) (A_star_coefficients f a) (A_star_coefficients f b))) t => x y.
change (f (paired_tensor (alg_bilinear W) a b (tensor_inj x y)) = paired_tensor (alg_bilinear Z) (A_star_coefficients f a) (A_star_coefficients f b) (tensor_inj x y)).
by rewrite !paired_tensorE !A_star_coefficientsE algebra_map_mul.
Qed.
(** Source for [A_star_coefficients_mul]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma A_star_coefficients_mul (a b : A) : A_star_coefficients f (alg_mul A a b) =
  alg_mul B (A_star_coefficients f a) (A_star_coefficients f b).
Proof.
apply: hom_finite_ext => x; rewrite A_star_coefficientsE !alternating_wedgeE.
exact: coefficients_paired_tensor.
Qed.
(** Source for [alternating_coefficient_map]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Definition or construction
    used to formalise this passage. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Definition alternating_coefficient_map : algebra_map A B.
Proof.
apply (@AlgebraMap K A B (GRing.Linear.clone _ _ _ _ (A_star_coefficients f) _)).
- change (A_star_coefficients f (coefficient_form V (alg_one W)) = coefficient_form V (alg_one Z)).
  by rewrite A_star_coefficients_constant algebra_map_one.
exact: A_star_coefficients_mul.
Defined.
End CoefficientAlgebraMap.

Section ScalarUnit.
Variable K : fieldType.
Variable W : algebra K.
(** Source for [scalar_unit]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition scalar_unit (c : K^o) := (c : K) *: alg_one W.
(** Source for [scalar_unit_linear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_unit_linear : linear scalar_unit.
Proof. move=> a c d; by rewrite /scalar_unit scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build K K^o W *:%R scalar_unit scalar_unit_linear.
(** Source for [scalar_unit_map]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition scalar_unit_map : algebra_map (scalar_algebra K) W.
Proof.
apply (@AlgebraMap K (scalar_algebra K) W (GRing.Linear.clone _ _ _ _ scalar_unit _)).
- exact: scale1r.
move=> a b; change ((a*b : K) *: alg_one W = alg_mul W (a *: alg_one W) (b *: alg_one W)).
by rewrite (bilZl (alg_bilinear W)) (bilZr (alg_bilinear W)) alg_unitl scalerA.
Defined.
End ScalarUnit.
