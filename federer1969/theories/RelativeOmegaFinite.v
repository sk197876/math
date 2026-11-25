(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import CentralTensor RelativeExterior RelativeGeneration
  CoefficientAction CoefficientCoordinates RelativeOmega OmegaConstruction OmegaFinite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, final assertion: the W-linear Omega is an
    isomorphism for finite-dimensional V, including V=0. *)
Section RelativeOmegaFinite.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Hypothesis hc : commutative (alg_mul W).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation rho := (@Hom_action K V W).
Local Notation R := (relative_exterior_algebra rho).
Local Notation E := (exterior_algebra (Hom V K^o)).
Local Notation T := (algebra_tensor W E).
Local Notation A := (alternating_unital_algebra h2 V W).
Local Notation j := (relative_generator rho).
Local Notation c := (relative_coefficient rho).
Local Notation L := (@scalar_base_lift K V W hc).
Local Notation O := (@Omega_relative K h2 V W hc).

(** Source for [Hom_action_unit_covector]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma Hom_action_unit_covector w a : Hom_action w (@unit_covector K V W a) = hom_with_coefficient w a.
Proof.
apply: hom_ext => v.
by rewrite Hom_actionE unit_covectorE hom_with_coefficientE (bilZr (alg_bilinear W)) alg_unitr.
Qed.
(** Source for [relative_generator_coordinates]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_generator_coordinates (a : Hom V W) :
  j a = \sum_i alg_mul R (c (a (e i))) (j (@unit_covector K V W (dual_basis he i))).
Proof.
rewrite {1}(finite_Hom_coefficients he a) linear_sum /=.
apply: eq_bigr => i _.
rewrite -Hom_action_unit_covector.
exact (@relative_generator_balance K W (Hom V W) rho (a (e i)) (@unit_covector K V W (dual_basis he i))).
Qed.
(** Source for [scalar_base_lift_generator_image]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_base_lift_generator_image a : algebra_image L (j a).
Proof.
rewrite relative_generator_coordinates; apply: algebra_image_sum => i.
exists (tensor_inj (a (e i)) (exterior_generator (dual_basis he i))).
by rewrite scalar_base_liftE scalar_relative_map_generator.
Qed.
(** Source for [scalar_base_lift_finite_surjective]: Federer (1969), 1.4.4,
    p. 20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Theorem scalar_base_lift_finite_surjective : forall x : R, exists t, L t = x.
Proof.
apply (@relative_generator_induction K W (Hom V W) rho (algebra_image L)).
- exact: algebra_image_zero.
- exact: algebra_image_add.
- exact: algebra_image_scale.
- move=> w; exists (@algebra_tensor_left K W E w); exact: scalar_base_lift_coefficient.
- exact: scalar_base_lift_generator_image.
- exact: algebra_image_mul.
Qed.
(** Source for [Omega_relative_finite_injective]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem Omega_relative_finite_injective : injective O.
Proof.
move=> x y hxy; have [t ht] := scalar_base_lift_finite_surjective (x-y).
have hz : O (L t) = 0 by rewrite ht linearB hxy subrr.
have ht0 : t = 0 := Omega_scalar_base_kernel hz.
have h : x-y = 0 by rewrite -ht ht0 linear0.
exact (subr0_eq h).
Qed.

(** Source for [scalar_base_image_form]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_base_image_form m (phi : A_m V W m) :
  algebra_image (algebra_comp O L) (form_include phi).
Proof.
pose hb := finite_e_lambda_basis he h2 m.
rewrite (included_coefficient_expansion hb phi); apply: algebra_image_sum => lambda.
pose b : A_m V K^o m := hom_to_form (dual_basis hb lambda).
have [x hx] := @Omega_finite_surjective K h2 V n e he (form_include b).
exists (tensor_inj (form_to_hom phi (e_lambda e (val lambda))) x).
apply: hom_finite_ext => v.
change (O (L (tensor_inj (form_to_hom phi (e_lambda e (val lambda))) x)) v =
  form_include (form_with_coefficient (form_to_hom phi (e_lambda e (val lambda))) b) v).
by rewrite Omega_scalar_baseE hx form_with_coefficient_includeE.
Qed.
(** Source for [Omega_relative_finite_surjective]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem Omega_relative_finite_surjective : forall a : A, exists x, O x = a.
Proof.
have hall : forall a : A, algebra_image (algebra_comp O L) a.
  apply (@alternating_sum_induction K V W (algebra_image (algebra_comp O L))).
  - exact: algebra_image_zero.
  - move=> x y hx hy; exact (@algebra_image_add K T A (algebra_comp O L) x y hx hy).
  exact: scalar_base_image_form.
move=> a; have [t ht] := hall a; exists (L t); exact: ht.
Qed.
(** Source for [Omega_relative_finite_bijective]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem Omega_relative_finite_bijective : bijective O.
Proof.
exists (linear_inverse Omega_relative_finite_injective Omega_relative_finite_surjective).
- exact: linear_inverseKV.
- exact: linear_inverseK.
Qed.
End RelativeOmegaFinite.
