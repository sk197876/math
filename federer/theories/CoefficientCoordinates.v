(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, finite-dimensional assertion with W coefficients:
    Grassmann coordinates take values in W. *)
Section HomCoefficients.
Variable K : fieldType.
Variables U W : lmodType K.
(** Source for [scalar_to_vector]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition scalar_to_vector (w : W) (a : K^o) := (a : K) *: w.
(** Source for [scalar_to_vector_linear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_to_vector_linear w : linear (scalar_to_vector w).
Proof. move=> a b c; by rewrite /scalar_to_vector scalerDl scalerA. Qed.
HB.instance Definition _ w := GRing.isLinear.Build K K^o W *:%R
  (scalar_to_vector w) (scalar_to_vector_linear w).
(** Source for [hom_with_coefficient]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition hom_with_coefficient w (f : Hom U K^o) : Hom U W :=
  hom_comp (hom_of_linear (GRing.Linear.clone _ _ _ _ (scalar_to_vector w) _)) f.
(** Source for [hom_with_coefficientE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma hom_with_coefficientE w f u : hom_with_coefficient w f u = (f u : K) *: w.
Proof. by []. Qed.

Variable I : finType.
(** Source for [hom_sum_coefficientsE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma hom_sum_coefficientsE (f : I -> Hom U W) v : (\sum_i f i) v = \sum_i f i v.
Proof. elim/big_ind2: _ => [|a b c d ha hb|i _]; by rewrite ?hom_zeroE ?hom_addE ?ha ?hb. Qed.
Variable e : I -> U.
Hypothesis he : is_basis e.
(** Source for [finite_Hom_coefficients]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma finite_Hom_coefficients (f : Hom U W) :
  f = \sum_i hom_with_coefficient (f (e i)) (dual_basis he i).
Proof.
apply: hom_ext => v; apply: (basis_linear_ext he (hom_as_linear f)
  (hom_as_linear (\sum_i hom_with_coefficient (f (e i)) (dual_basis he i)))) v => j.
change (f (e j) = (\sum_i hom_with_coefficient (f (e i)) (dual_basis he i)) (e j)).
rewrite hom_sum_coefficientsE.
under eq_bigr do rewrite hom_with_coefficientE dual_basisE.
rewrite (bigD1 j) //= eqxx scale1r.
have hz : (\sum_(i | i != j) (if j == i then 1 else 0 : K) *: f (e i)) = 0.
  apply: big1 => i hi; by rewrite eq_sym (negbTE hi) scale0r.
by rewrite hz addr0.
Qed.
End HomCoefficients.

Section FormCoefficients.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
(** Source for [form_with_coefficient]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition form_with_coefficient w (phi : A_m V K^o m) : A_m V W m :=
  hom_to_form (hom_with_coefficient w (form_to_hom phi)).
(** Source for [form_include_hom_to_form]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma form_include_hom_to_form (f : Hom (exterior_power V m) W) x :
  form_include (hom_to_form f) x = f (component (exterior_grading V) m x).
Proof. by rewrite /form_include /hom_to_form homogeneous_formK homogeneous_includeE homogeneous_extendE. Qed.
(** Source for [form_with_coefficient_includeE]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma form_with_coefficient_includeE w phi x :
  form_include (form_with_coefficient w phi) x = (form_include phi x : K) *: w.
Proof.
rewrite /form_with_coefficient form_include_hom_to_form hom_with_coefficientE.
rewrite -{2}(form_to_homK phi).
by rewrite /form_include /hom_to_form homogeneous_formK homogeneous_includeE homogeneous_extendE.
Qed.
Variable I : finType.
Variable e : I -> exterior_power V m.
Hypothesis he : is_basis e.
(** Source for [form_coefficient_expansion]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem form_coefficient_expansion (phi : A_m V W m) :
  phi = \sum_i form_with_coefficient (form_to_hom phi (e i)) (hom_to_form (dual_basis he i)).
Proof.
rewrite -{1}(form_to_homK phi) {1}(finite_Hom_coefficients he (form_to_hom phi)) linear_sum /=.
apply: eq_bigr => i _; by rewrite /form_with_coefficient hom_to_formK.
Qed.
(** Source for [included_coefficient_expansion]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Theorem included_coefficient_expansion (phi : A_m V W m) :
  form_include phi = \sum_i form_include (form_with_coefficient
    (form_to_hom phi (e i)) (hom_to_form (dual_basis he i))).
Proof. by rewrite -linear_sum -form_coefficient_expansion. Qed.
End FormCoefficients.
