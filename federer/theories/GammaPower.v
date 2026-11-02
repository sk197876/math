(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import HomTensor Gamma TraceAlgebra TraceComponents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: the second occurrence of Gamma, on the m-th
    exterior powers, is the inverse of the displayed natural maps.
    The construction uses 1.4.1 before choosing any coordinates. *)
Section GammaPower.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation F := (A_m V K^o m).
Local Notation X := (exterior_power V m).
Local Notation Y := (exterior_power W m).
Local Notation up := (GRing.Linear.clone _ _ _ _ (@hom_to_form K V K^o m) _).
Local Notation down := (GRing.Linear.clone _ _ _ _ (@form_to_hom K V K^o m) _).
(** Source for [Gamma_m_inverse]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Definition or construction used to formalise this passage. *)
Definition Gamma_m_inverse : {linear tensor_space F Y -> Hom X Y} :=
  linear_comp (@tensor_Hom K X Y) (tensor_map down (linear_id Y)).
(** Source for [Gamma_m_inverseE]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_m_inverseE phi xi eta :
  Gamma_m_inverse (tensor_inj phi xi) eta = (pairing eta phi : K) *: xi.
Proof.
change (@tensor_Hom K X Y (tensor_map down (linear_id Y) (tensor_inj phi xi)) eta =
  (pairing eta phi : K) *: xi).
by rewrite tensor_mapE tensor_HomE.
Qed.
Variable I : finType.
Variable e : I -> X.
Hypothesis he : is_basis e.
(** Source for [Gamma_m]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Definition or construction used to formalise this passage. *)
Definition Gamma_m : {linear Hom X Y -> tensor_space F Y} :=
  linear_comp (tensor_map up (linear_id Y))
    (GRing.Linear.clone _ _ _ _ (@Hom_tensor K X Y I e he) _).
(** Source for [Gamma_mE]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma Gamma_mE f : Gamma_m f =
  \sum_i tensor_inj (hom_to_form (dual_basis he i)) (f (e i)).
Proof.
change (tensor_map up (linear_id Y) (\sum_i tensor_inj (dual_basis he i) (f (e i))) =
  \sum_i tensor_inj (hom_to_form (dual_basis he i)) (f (e i))).
rewrite linear_sum; apply: eq_bigr => i _; exact: tensor_mapE.
Qed.
(** Source for [Gamma_m_up_down]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_m_up_down t :
  tensor_map down (linear_id Y) (tensor_map up (linear_id Y) t) = t.
Proof.
elim/tensor_induction: t => [|x y hx hy|c x hx|a w].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : tensor_space (Hom X K^o) Y => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : tensor_space (Hom X K^o) Y => c *: x) hx).
by rewrite !tensor_mapE /= hom_to_formK.
Qed.
(** Source for [Gamma_m_down_up]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_m_down_up t :
  tensor_map up (linear_id Y) (tensor_map down (linear_id Y) t) = t.
Proof.
elim/tensor_induction: t => [|x y hx hy|c x hx|a w].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : tensor_space F Y => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : tensor_space F Y => c *: x) hx).
by rewrite !tensor_mapE /= form_to_homK.
Qed.
(** Source for [Gamma_mK]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma Gamma_mK : cancel Gamma_m Gamma_m_inverse.
Proof.
exact (can_comp Gamma_m_up_down (@Hom_tensorK K X Y I e he)).
Qed.
(** Source for [Gamma_m_inverseK]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_m_inverseK : cancel Gamma_m_inverse Gamma_m.
Proof.
exact (can_comp (@tensor_HomK K X Y I e he) Gamma_m_down_up).
Qed.
(** Source for [Gamma_m_isomorphism]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Theorem Gamma_m_isomorphism : bijective Gamma_m.
Proof. exists Gamma_m_inverse; [exact: Gamma_mK | exact: Gamma_m_inverseK]. Qed.
End GammaPower.

(** Federer 1.4.5, divided-power display: identify the coordinate
    covectors with the actual alternating products omega_lambda. *)
Section GammaCoordinates.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation omega := (fun i => one_form (dual_basis he i)).
(** Source for [Gamma_dualE]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma Gamma_dualE i j : omega i [tuple e j] = if i == j then 1 else 0.
Proof. by rewrite one_formE dual_basisE eq_sym. Qed.
(** Source for [Gamma_coordinate]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma Gamma_coordinate m (lambda : Lambda n m) :
  hom_to_form (dual_basis (finite_e_lambda_basis he h2 m) lambda) =
  omega_lambda h2 omega lambda.
Proof.
apply: (@pairing_basis_ext K h2 V n m e he) => mu.
by rewrite /pairing hom_to_formK dual_basisE -/(pairing _ _)
  (pairing_e_omega h2 Gamma_dualE) eq_sym.
Qed.
(** Source for [Gamma_power]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Definition or construction used to formalise this passage. *)
Definition Gamma_power m : {linear Hom (exterior_power V m) (exterior_power W m) ->
  tensor_space (A_m V K^o m) (exterior_power W m)} :=
  @Gamma_m K V W m (Finite.clone (Lambda n m) _)
    (@finite_e_lambda K n V e m) (finite_e_lambda_basis he h2 m).
(** Source for [Gamma_powerE]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem Gamma_powerE m f : Gamma_power m f =
  \sum_(lambda : Lambda n m) tensor_inj (omega_lambda h2 omega lambda)
    (f (e_lambda e (val lambda))).
Proof.
rewrite /Gamma_power Gamma_mE; apply: eq_bigr => lambda _.
by rewrite Gamma_coordinate.
Qed.
(** Source for [Gamma_power_A]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Definition or construction used to formalise this passage. *)
Definition Gamma_power_A m : {linear Hom (exterior_power V m) (exterior_power W m) -> A h2 V W} :=
  linear_comp (@A_component K h2 V W m) (Gamma_power m).
(** Source for [Gamma_power_AE]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma Gamma_power_AE m f : Gamma_power_A m f =
  \sum_(lambda : Lambda n m) A_pure h2 (omega_lambda h2 omega lambda)
    (f (e_lambda e (val lambda))).
Proof.
change (@A_component K h2 V W m (Gamma_power m f) =
  \sum_(lambda : Lambda n m) A_pure h2 (omega_lambda h2 omega lambda)
    (f (e_lambda e (val lambda)))).
rewrite Gamma_powerE linear_sum; apply: eq_bigr => lambda _.
exact: A_componentE.
Qed.
End GammaCoordinates.
