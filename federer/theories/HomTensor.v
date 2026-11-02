(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CoefficientCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.4, recalled in 1.4.5: the natural isomorphism
    Hom(V,K) tensor W -> Hom(V,W) when V is finite-dimensional. *)
Section HomTensor.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [hom_tensor_pair]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Definition or construction used to formalise this passage. *)
Definition hom_tensor_pair (a : Hom V K^o) (w : W) := hom_with_coefficient w a.
(** Source for [hom_tensor_bilinear]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma hom_tensor_bilinear : bilinear hom_tensor_pair.
Proof.
split=> [w c a b|a c w z]; apply: hom_ext => v.
- change (((c*a v+b v : K) *: w) = c *: ((a v : K) *: w)+(b v : K) *: w).
  by rewrite scalerDl scalerA.
- change ((a v : K) *: (c *: w+z) = c *: ((a v : K) *: w)+(a v : K) *: z).
  by rewrite scalerDr !scalerA mulrC.
Qed.
(** Source for [tensor_Hom]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Definition or construction used to formalise this passage. *)
Definition tensor_Hom : {linear tensor_space (Hom V K^o) W -> Hom V W} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift hom_tensor_bilinear) _.
(** Source for [tensor_HomE]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_HomE a w v : tensor_Hom (tensor_inj a w) v = (a v : K) *: w.
Proof.
have h : tensor_Hom (tensor_inj a w) = hom_tensor_pair a w := tensor_liftE hom_tensor_bilinear a w.
exact (congr1 (fun f : Hom V W => f v) h).
Qed.

Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [Hom_tensor]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Definition or construction used to formalise this passage. *)
Definition Hom_tensor (f : Hom V W) := \sum_i tensor_inj (dual_basis he i) (f (e i)).
(** Source for [Hom_tensor_linear]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma Hom_tensor_linear : linear Hom_tensor.
Proof.
move=> c f g; rewrite /Hom_tensor.
under eq_bigr do rewrite hom_addE hom_scaleE tensor_inj_addr tensor_inj_scaler.
by rewrite big_split scaler_sumr.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom V W)
  (tensor_space (Hom V K^o) W) *:%R Hom_tensor Hom_tensor_linear.
(** Source for [Hom_tensorK]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma Hom_tensorK : cancel Hom_tensor tensor_Hom.
Proof.
move=> f; rewrite /Hom_tensor linear_sum /=.
transitivity (\sum_i hom_with_coefficient (f (e i)) (dual_basis he i)).
- apply: eq_bigr => i _; exact: tensor_liftE.
exact (esym (finite_Hom_coefficients he f)).
Qed.
(** Source for [tensor_HomK]: Federer (1969), 1.1.4, p. 11, opening
    paragraph, the natural transformation Phi. In words: The map from
    Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_HomK : cancel tensor_Hom Hom_tensor.
Proof.
apply: tensor_induction => [|x y hx hy|c x hx|a w].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 (fun x y : tensor_space (Hom V K^o) W => x+y) hx hy).
- rewrite !linearZ; exact (congr1 (fun x : tensor_space (Hom V K^o) W => c *: x) hx).
rewrite /Hom_tensor.
under eq_bigr do rewrite tensor_HomE tensor_inj_scaler -tensor_inj_scalel.
have ht : (\sum_i tensor_inj ((a (e i) : K) *: dual_basis he i) w) =
    tensor_inj (\sum_i (a (e i) : K) *: dual_basis he i) w.
  elim/big_ind2: _ => [|x y z t hx hy|i _]; by rewrite ?tensor_inj0l ?tensor_inj_addl ?hx ?hy.
rewrite ht; congr tensor_inj; apply: hom_ext => v.
apply: (basis_linear_ext he
  (hom_as_linear (\sum_i (a (e i) : K) *: dual_basis he i)) (hom_as_linear a)) v => i.
exact: dual_sum_evaluate.
Qed.
(** Source for [tensor_Hom_isomorphism]: Federer (1969), 1.1.4, p. 11,
    opening paragraph, the natural transformation Phi. In words: The map
    from Hom(V,R) tensor W to Hom(V,W) sends alpha tensor y to the map x to
    alpha(x)y; it is injective and is surjective when either space is finite
    dimensional. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem tensor_Hom_isomorphism : bijective tensor_Hom.
Proof. exists Hom_tensor; [exact: tensor_HomK | exact: Hom_tensorK]. Qed.
End HomTensor.
