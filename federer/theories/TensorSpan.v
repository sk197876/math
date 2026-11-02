(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP ModuleQuotient TensorProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Spanning.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [tensor_inj0l]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma tensor_inj0l (w : W) : tensor_inj (0 : V) w = 0.
Proof. by have := tensor_inj_scalel 0 (0 : V) w; rewrite !scale0r. Qed.

(** Source for [tensor_inj0r]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma tensor_inj0r (v : V) : tensor_inj v (0 : W) = 0.
Proof. by have := tensor_inj_scaler 0 v (0 : W); rewrite !scale0r. Qed.

(** Source for [tensor_balance]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma tensor_balance a (v : V) (w : W) :
  tensor_inj (a *: v) w = tensor_inj v (a *: w).
Proof. by rewrite tensor_inj_scalel tensor_inj_scaler. Qed.

(** Source for [pure_tensor_combination]: Federer (1969), 1.1.1, p. 9,
    universal property and quotient existence proof. In words: The tensor
    product represents multilinear maps; its construction is the quotient of
    the finitely supported free space by the multilinearity relations.
    Definition or construction used to formalise this passage. *)
Definition pure_tensor_combination (t : tensor_space V W) : Prop :=
  exists s : seq (K * (V * W)), t = \sum_(p <- s) p.1 *: tensor_inj p.2.1 p.2.2.

(** Source for [pure_tensor_combination0]: Federer (1969), 1.1.1, p. 9,
    universal property and quotient existence proof. In words: The tensor
    product represents multilinear maps; its construction is the quotient of
    the finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_tensor_combination0 : pure_tensor_combination 0.
Proof. by exists [::]; rewrite big_nil. Qed.

(** Source for [pure_tensor_combinationD]: Federer (1969), 1.1.1, p. 9,
    universal property and quotient existence proof. In words: The tensor
    product represents multilinear maps; its construction is the quotient of
    the finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_tensor_combinationD t u :
  pure_tensor_combination t -> pure_tensor_combination u ->
  pure_tensor_combination (t + u).
Proof. by move=> [s ->] [r ->]; exists (s ++ r); rewrite big_cat. Qed.

(** Source for [pure_tensor_combinationZ]: Federer (1969), 1.1.1, p. 9,
    universal property and quotient existence proof. In words: The tensor
    product represents multilinear maps; its construction is the quotient of
    the finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_tensor_combinationZ a t :
  pure_tensor_combination t -> pure_tensor_combination (a *: t).
Proof.
move=> [s ->]; exists [seq (a * p.1, p.2) | p <- s].
rewrite big_map scaler_sumr; apply: eq_bigr => p _.
by rewrite scalerA.
Qed.

(** Source for [pure_tensor_subspace]: Federer (1969), 1.1.1, p. 9,
    universal property and quotient existence proof. In words: The tensor
    product represents multilinear maps; its construction is the quotient of
    the finitely supported free space by the multilinearity relations.
    Definition or construction used to formalise this passage. *)
Definition pure_tensor_subspace : subspace (tensor_space V W) :=
  @Subspace K (tensor_space V W) pure_tensor_combination pure_tensor_combination0
    pure_tensor_combinationD pure_tensor_combinationZ.

(** Every element is a finite sum of scalar multiples of pure tensors. The
    proof uses only the universal property. *)
(** Source for [tensor_span]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Theorem tensor_span t : pure_tensor_combination t.
Proof.
pose Q := module_quotient pure_tensor_subspace.
pose p : {linear tensor_space V W -> Q} :=
  GRing.Linear.clone _ _ _ _ (quotient_projection pure_tensor_subspace) _.
pose z : {linear tensor_space V W -> Q} :=
  GRing.Linear.clone _ _ _ _ (\0 : tensor_space V W -> Q) _.
have e := tensor_ext (tensor_exists V W) p z.
have /quotient_projection_eq : quotient_projection pure_tensor_subspace t =
    quotient_projection pure_tensor_subspace 0.
  rewrite linear0; apply: e => v w /=.
  rewrite -(linear0 (quotient_projection pure_tensor_subspace)).
  apply/quotient_projection_eq; rewrite subr0.
  by exists [:: (1, (v, w))]; rewrite big_seq1 scale1r.
by rewrite subr0.
Qed.

(** Source for [tensor_induction]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma tensor_induction (P : tensor_space V W -> Prop)
    (h0 : P 0) (hadd : forall x y, P x -> P y -> P (x + y))
    (hscale : forall a x, P x -> P (a *: x))
    (hpure : forall v w, P (tensor_inj v w)) :
  forall t, P t.
Proof.
move=> t; have [s ->] := tensor_span t.
by apply: big_ind => // p _; exact: hscale (hpure p.2.1 p.2.2).
Qed.
End Spanning.
