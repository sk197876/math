(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import Gamma GammaPower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: naturality of the displayed Hom-tensor
    identifications, under precomposition and postcomposition. *)
Section Naturality.
Variable K : fieldType.
Variables V W V' W' : lmodType K.
Variables (a : {linear V' -> V}) (b : {linear W -> W'}).
(** Source for [Hom_sandwich]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Definition or construction used to formalise this
    passage. *)
Definition Hom_sandwich (f : Hom V W) : Hom V' W' :=
  hom_comp (hom_of_linear b) (hom_comp f (hom_of_linear a)).
(** Source for [Hom_sandwichE]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Hom_sandwichE f v : Hom_sandwich f v = b (f (a v)).
Proof. by []. Qed.
(** Source for [Hom_sandwich_linear]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Hom_sandwich_linear : linear Hom_sandwich.
Proof.
move=> c f g; apply: hom_ext => v.
by rewrite !Hom_sandwichE !hom_addE !hom_scaleE (linD (linearP b)) (linZ (linearP b)).
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom V W) (Hom V' W') *:%R
  Hom_sandwich Hom_sandwich_linear.
Local Notation dual_a := (GRing.Linear.clone _ _ _ _ (@A_m_dual K V' V K^o a 1) _).
(** Source for [Gamma_inverse_natural]: Federer (1969), 1.4.5, p. 20,
    natural Hom-tensor isomorphism and dual-basis formula for Gamma. In
    words: For finite-dimensional V, the inverse Gamma of the Hom-tensor
    identification sends f to the sum of each dual basic covector tensored
    with the image of its basis vector. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma Gamma_inverse_natural t :
  @Gamma_inverse K V' W' (tensor_map dual_a b t) = Hom_sandwich (@Gamma_inverse K V W t).
Proof.
apply: (tensor_ext (tensor_exists (A_m V K^o 1) W)
  (linear_comp (@Gamma_inverse K V' W') (tensor_map dual_a b))
  (linear_comp (GRing.Linear.clone _ _ _ _ Hom_sandwich _) (@Gamma_inverse K V W))) t => phi w.
apply: hom_ext => v.
change (@Gamma_inverse K V' W' (tensor_map dual_a b (tensor_inj phi w)) v =
  Hom_sandwich (@Gamma_inverse K V W (tensor_inj phi w)) v).
rewrite tensor_mapE Gamma_inverseE Hom_sandwichE Gamma_inverseE (linZ (linearP b)).
rewrite !one_homE A_m_dualE.
have h : map_tuple a [tuple v] = [tuple a v] by apply: val_inj.
by rewrite h.
Qed.
Variables I J : finType.
Variables (e : I -> V) (d : J -> V').
Hypotheses (he : is_basis e) (hd : is_basis d).
(** Source for [Gamma_natural]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem Gamma_natural f :
  @Gamma K V' W' J d hd (Hom_sandwich f) =
  tensor_map dual_a b (@Gamma K V W I e he f).
Proof.
apply (can_inj (@Gamma_inverseK K V' W' J d hd)).
by rewrite GammaK Gamma_inverse_natural GammaK.
Qed.
End Naturality.

(** Federer 1.4.5: the same naturality holds for Gamma on exterior
    powers; here the natural pairing of 1.4.1 supplies the proof. *)
Section PowerNaturality.
Variable K : fieldType.
Variables V W V' W' : lmodType K.
Variables (a : {linear V' -> V}) (b : {linear W -> W'}).
Variable m : nat.
Local Notation dual_a := (GRing.Linear.clone _ _ _ _ (@A_m_dual K V' V K^o a m) _).
Local Notation a_m := (exterior_power_map a m).
Local Notation b_m := (exterior_power_map b m).
(** Source for [Gamma_m_inverse_natural]: Federer (1969), 1.4.5, p. 20,
    natural Hom-tensor isomorphism and dual-basis formula for Gamma. In
    words: For finite-dimensional V, the inverse Gamma of the Hom-tensor
    identification sends f to the sum of each dual basic covector tensored
    with the image of its basis vector. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma Gamma_m_inverse_natural t :
  @Gamma_m_inverse K V' W' m (tensor_map dual_a b_m t) =
    Hom_sandwich a_m b_m (@Gamma_m_inverse K V W m t).
Proof.
apply: (tensor_ext (tensor_exists (A_m V K^o m) (exterior_power W m))
  (linear_comp (@Gamma_m_inverse K V' W' m) (tensor_map dual_a b_m))
  (linear_comp (GRing.Linear.clone _ _ _ _ (Hom_sandwich a_m b_m) _) (@Gamma_m_inverse K V W m))) t => phi xi.
apply: hom_ext => eta.
change (@Gamma_m_inverse K V' W' m (tensor_map dual_a b_m (tensor_inj phi xi)) eta =
  Hom_sandwich a_m b_m (@Gamma_m_inverse K V W m (tensor_inj phi xi)) eta).
rewrite tensor_mapE Gamma_m_inverseE Hom_sandwichE Gamma_m_inverseE (linZ (linearP b_m)).
by rewrite A_m_dual_pairing.
Qed.
Variables I J : finType.
Variables (e : I -> exterior_power V m) (d : J -> exterior_power V' m).
Hypotheses (he : is_basis e) (hd : is_basis d).
(** Source for [Gamma_m_natural]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem Gamma_m_natural f :
  @Gamma_m K V' W' m J d hd (Hom_sandwich a_m b_m f) =
  tensor_map dual_a b_m (@Gamma_m K V W m I e he f).
Proof.
apply (can_inj (@Gamma_m_inverseK K V' W' m J d hd)).
by rewrite Gamma_mK Gamma_m_inverse_natural Gamma_mK.
Qed.
End PowerNaturality.
