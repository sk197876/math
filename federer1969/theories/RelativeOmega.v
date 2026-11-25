(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification CentralTensor RelativeExterior CoefficientAction AlternatingCoefficientMap
  OmegaConstruction OmegaInjective TensorEvaluation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, final parenthesis: Omega over the commutative
    coefficient algebra W. Its W-linearity follows from its values on
    coefficients and multiplicativity. *)
Section RelativeOmega.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Hypothesis hc : commutative (alg_mul W).
Local Notation rho := (@Hom_action K V W).
Local Notation R := (relative_exterior_algebra rho).
Local Notation A := (alternating_unital_algebra h2 V W).
Local Notation c := (relative_coefficient rho).
Local Notation j := (relative_generator rho).
(** Source for [Omega_relative]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition Omega_relative : algebra_map R A :=
  @relative_extension K W (Hom V W) rho A (@coefficient_algebra_map K h2 V W)
    (GRing.Linear.clone _ _ _ _ (@one_generator K V W) _)
    (@coefficient_central K h2 V W hc)
    (@one_generator_balance K h2 V W) (@one_generator_square_zero K h2 V W hc).
(** Source for [Omega_relative_coefficient]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Lemma Omega_relative_coefficient w : Omega_relative (c w) = coefficient_form V w.
Proof. exact: relative_extension_coefficient. Qed.
(** Source for [Omega_relative_generator]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Lemma Omega_relative_generator a : Omega_relative (j a) = one_generator a.
Proof. exact: relative_extension_generator. Qed.
(** Source for [Omega_relative_W_linear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Formalises the indicated part of the
    passage under the hypotheses in the statement below. The local LaTeX
    erratum, p. 1, entry for book p. 20 line 11, changes the printed wording
    to in case. *)
Lemma Omega_relative_W_linear w x :
  Omega_relative (@relative_action K W (Hom V W) rho w x) = alg_mul A (coefficient_form V w) (Omega_relative x).
Proof. by rewrite /relative_action algebra_map_mul Omega_relative_coefficient. Qed.
(** Source for [Omega_relative_unique]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Formalises the indicated part of the
    passage under the hypotheses in the statement below. The local LaTeX
    erratum, p. 1, entry for book p. 20 line 11, changes the printed wording
    to in case. *)
Theorem Omega_relative_unique (g : algebra_map R A) :
  (forall w, g (c w) = coefficient_form V w) ->
  (forall a, g (j a) = one_generator a) -> forall x, g x = Omega_relative x.
Proof.
exact (@relative_extension_unique K W (Hom V W) rho A (@coefficient_algebra_map K h2 V W)
  (GRing.Linear.clone _ _ _ _ (@one_generator K V W) _)
  (@coefficient_central K h2 V W hc) (@one_generator_balance K h2 V W)
  (@one_generator_square_zero K h2 V W hc) g).
Qed.
(** Source for [relative_Hom_exterior_exists]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem relative_Hom_exterior_exists : is_relative_exterior_algebra rho c j.
Proof. exact (@relative_exterior_exists K W hc (Hom V W) rho). Qed.

(** Source for [unit_covector]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition unit_covector (a : Hom V K^o) : Hom V W := hom_comp (hom_of_linear (scalar_unit_map W)) a.
(** Source for [unit_covectorE]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma unit_covectorE a v : unit_covector a v = (a v : K) *: alg_one W.
Proof. by []. Qed.
(** Source for [unit_covector_linear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma unit_covector_linear : linear unit_covector.
Proof.
move=> b a d; apply: hom_ext => v.
change ((b*a v+d v : K) *: alg_one W = b *: ((a v : K) *: alg_one W) + (d v : K) *: alg_one W).
by rewrite scalerDl scalerA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom V K^o) (Hom V W)
  *:%R unit_covector unit_covector_linear.
Local Notation E := (exterior_algebra (Hom V K^o)).
Local Notation T := (algebra_tensor W E).
(** Source for [scalar_relative_generator]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Definition or construction
    used to formalise this passage. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Definition scalar_relative_generator : {linear Hom V K^o -> R} :=
  linear_comp j (GRing.Linear.clone _ _ _ _ unit_covector _).
(** Source for [scalar_relative_square]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_relative_square a : alg_mul R (scalar_relative_generator a) (scalar_relative_generator a) = 0.
Proof. exact: relative_generator_square. Qed.
(** Source for [scalar_relative_map]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition scalar_relative_map : algebra_map E R := exterior_algebra_extension scalar_relative_square.
(** Source for [scalar_relative_map_generator]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_relative_map_generator a : scalar_relative_map (exterior_generator a) = j (unit_covector a).
Proof. exact: exterior_algebra_extension_generator. Qed.
(** Source for [scalar_base_lift]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition scalar_base_lift : algebra_map T R :=
  central_tensor_map (fun w x => @relative_coefficient_central K W hc (Hom V W) rho w (scalar_relative_map x)).
(** Source for [scalar_base_liftE]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_base_liftE w x : scalar_base_lift (tensor_inj w x) = alg_mul R (c w) (scalar_relative_map x).
Proof. exact: central_tensorE. Qed.
(** Source for [scalar_base_lift_coefficient]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_base_lift_coefficient w : scalar_base_lift (@algebra_tensor_left K W E w) = c w.
Proof. exact: central_tensor_left. Qed.
(** Source for [scalar_base_lift_generator]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma scalar_base_lift_generator a :
  scalar_base_lift (@algebra_tensor_right K W E (exterior_generator a)) = j (unit_covector a).
Proof. exact (eq_trans (central_tensor_right _ _) (scalar_relative_map_generator a)). Qed.

Local Notation S := (alternating_unital_algebra h2 V (scalar_algebra K)).
(** Source for [Omega_coefficients]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition Omega_coefficients : algebra_map E A :=
  algebra_comp (alternating_coefficient_map h2 V (scalar_unit_map W)) (Omega h2 V).
(** Source for [Omega_coefficientsE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_coefficientsE x v : Omega_coefficients x v = (Omega h2 V x v : K) *: alg_one W.
Proof. by []. Qed.
(** Source for [Omega_relative_scalar]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_relative_scalar x : Omega_relative (scalar_relative_map x) = Omega_coefficients x.
Proof.
apply: (@exterior_algebra_ext K (Hom V K^o) E
  (GRing.Linear.clone _ _ _ _ (@exterior_generator K (Hom V K^o)) _)
  (exterior_algebra_exists _) A (algebra_comp Omega_relative scalar_relative_map) Omega_coefficients) x => a.
change (Omega_relative (scalar_relative_map (exterior_generator a)) =
  A_star_coefficients (scalar_unit_map W) (Omega h2 V (exterior_generator a))).
by rewrite scalar_relative_map_generator Omega_relative_generator Omega_generator A_star_coefficients_one.
Qed.
(** Source for [Omega_scalar_baseE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_scalar_baseE w x v : Omega_relative (scalar_base_lift (tensor_inj w x)) v =
  (Omega h2 V x v : K) *: w.
Proof.
rewrite scalar_base_liftE algebra_map_mul Omega_relative_coefficient Omega_relative_scalar.
by rewrite coefficient_product_leftE Omega_coefficientsE (bilZr (alg_bilinear W)) alg_unitr.
Qed.
(** Source for [Omega_as_Hom]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition Omega_as_Hom (x : E) : Hom (exterior_space V) K^o := Omega h2 V x.
(** Source for [Omega_as_Hom_linear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_as_Hom_linear : linear Omega_as_Hom.
Proof. move=> a x y; apply: hom_ext => v; by rewrite /Omega_as_Hom (linearP (Omega h2 V)). Qed.
HB.instance Definition _ := GRing.isLinear.Build K E (Hom (exterior_space V) K^o)
  *:%R Omega_as_Hom Omega_as_Hom_linear.
(** Source for [Omega_as_Hom_injective]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_as_Hom_injective : injective Omega_as_Hom.
Proof. move=> x y h; apply (@Omega_injective K h2 V x y); apply: hom_finite_ext => v; exact (congr1 (fun f : Hom (exterior_space V) K^o => f v) h). Qed.
(** Source for [Omega_scalar_base_tensor]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_scalar_base_tensor t v : Omega_relative (scalar_base_lift t) v =
  tensor_evaluation W (GRing.Linear.clone _ _ _ _ Omega_as_Hom _) v t.
Proof.
elim/tensor_induction: t => [|t u ht hu|a t ht|w x].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : W => x+y) ht hu).
- rewrite !linearZ; exact (congr1 (fun x : W => a *: x) ht).
by rewrite Omega_scalar_baseE tensor_evaluationE.
Qed.
(** Source for [Omega_scalar_base_kernel]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma Omega_scalar_base_kernel t : Omega_relative (scalar_base_lift t) = 0 -> t = 0.
Proof.
move=> ht; apply (tensor_evaluation_separates Omega_as_Hom_injective) => v.
by rewrite -Omega_scalar_base_tensor ht hom_finite_zeroE.
Qed.
End RelativeOmega.
