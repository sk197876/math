(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import HomTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: the natural map A^1 V tensor W -> Hom(V,W),
    and its inverse Gamma with the displayed dual-basis formula. *)
Section Gamma.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation F := (A_m V K^o 1).
Local Notation H := (Hom V K^o).
Local Notation up := (GRing.Linear.clone _ _ _ _ (@one_form K V K^o) _).
Local Notation down := (GRing.Linear.clone _ _ _ _ (@one_hom K V K^o) _).
(** Source for [Gamma_inverse]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Definition or construction used to formalise this
    passage. *)
Definition Gamma_inverse : {linear tensor_space F W -> Hom V W} :=
  linear_comp (@tensor_Hom K V W) (tensor_map down (linear_id W)).
(** Source for [Gamma_inverseE]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Gamma_inverseE a w v : Gamma_inverse (tensor_inj a w) v = (one_hom a v : K) *: w.
Proof.
change (@tensor_Hom K V W (tensor_map down (linear_id W) (tensor_inj a w)) v = (one_hom a v : K) *: w).
by rewrite tensor_mapE tensor_HomE.
Qed.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [Gamma]: Federer (1969), 1.4.5, p. 20, natural Hom-tensor
    isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Definition or construction used to formalise this
    passage. *)
Definition Gamma : {linear Hom V W -> tensor_space F W} :=
  linear_comp (tensor_map up (linear_id W))
    (GRing.Linear.clone _ _ _ _ (@Hom_tensor K V W I e he) _).
(** Source for [GammaE]: Federer (1969), 1.4.5, p. 20, natural Hom-tensor
    isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma GammaE f : Gamma f = \sum_i tensor_inj (one_form (dual_basis he i)) (f (e i)).
Proof.
change (tensor_map up (linear_id W) (\sum_i tensor_inj (dual_basis he i) (f (e i))) = \sum_i tensor_inj (one_form (dual_basis he i)) (f (e i))).
rewrite linear_sum; apply: eq_bigr => i _.
change (tensor_map up (linear_id W) (tensor_inj (dual_basis he i) (f (e i))) = tensor_inj (one_form (dual_basis he i)) (f (e i))).
exact: tensor_mapE.
Qed.
(** Source for [Gamma_up_down]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Gamma_up_down t : tensor_map down (linear_id W) (tensor_map up (linear_id W) t) = t.
Proof.
elim/tensor_induction: t => [|x y hx hy|c x hx|a w].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : tensor_space H W => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : tensor_space H W => c *: x) hx).
change (tensor_map down (linear_id W) (tensor_map up (linear_id W) (tensor_inj a w)) = tensor_inj a w).
by rewrite !tensor_mapE /= one_formK.
Qed.
(** Source for [Gamma_down_up]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Gamma_down_up t : tensor_map up (linear_id W) (tensor_map down (linear_id W) t) = t.
Proof.
elim/tensor_induction: t => [|x y hx hy|c x hx|a w].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : tensor_space F W => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : tensor_space F W => c *: x) hx).
by rewrite !tensor_mapE /= one_homK.
Qed.
(** Source for [GammaK]: Federer (1969), 1.4.5, p. 20, natural Hom-tensor
    isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma GammaK : cancel Gamma Gamma_inverse.
Proof.
move=> f; change (@tensor_Hom K V W (tensor_map down (linear_id W)
  (tensor_map up (linear_id W) (@Hom_tensor K V W I e he f))) = f).
by rewrite Gamma_up_down Hom_tensorK.
Qed.
(** Source for [Gamma_inverseK]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma Gamma_inverseK : cancel Gamma_inverse Gamma.
Proof.
move=> t; change (tensor_map up (linear_id W) (@Hom_tensor K V W I e he
  (@tensor_Hom K V W (tensor_map down (linear_id W) t))) = t).
by rewrite tensor_HomK Gamma_down_up.
Qed.
(** Source for [Gamma_isomorphism]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem Gamma_isomorphism : bijective Gamma.
Proof. exists Gamma_inverse; [exact: GammaK | exact: Gamma_inverseK]. Qed.
End Gamma.
