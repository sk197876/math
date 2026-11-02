(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP ModuleQuotient FamilyUpdate TensorFamilyUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.1: the m-fold products span the tensor product. The proof
    uses only the universal property. *)
Section Spanning.
Variable K : fieldType.
Variable m : nat.
Variable V : 'I_m -> lmodType K.
Variable T : lmodType K.
Variable mu : {dffun forall i, V i} -> T.
Hypothesis H : is_tensor_product_family mu.

(** Source for [pure_combination]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Definition or construction used to formalise this passage. *)
Definition pure_combination (t : T) : Prop :=
  exists s : seq (K * {dffun forall i, V i}), t = \sum_(p <- s) p.1 *: mu p.2.

(** Source for [pure_combination0]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_combination0 : pure_combination 0.
Proof. by exists [::]; rewrite big_nil. Qed.

(** Source for [pure_combinationD]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_combinationD t u :
  pure_combination t -> pure_combination u -> pure_combination (t + u).
Proof.
move=> [s ->] [r ->]; exists (s ++ r).
by rewrite big_cat.
Qed.

(** Source for [pure_combinationZ]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_combinationZ a t : pure_combination t -> pure_combination (a *: t).
Proof.
move=> [s ->]; exists [seq (a * p.1, p.2) | p <- s].
rewrite big_map scaler_sumr; apply: eq_bigr => p _.
by rewrite scalerA.
Qed.

(** Source for [pure_subspace]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Definition or construction used to formalise this passage. *)
Definition pure_subspace : subspace T :=
  @Subspace K T pure_combination pure_combination0 pure_combinationD
    pure_combinationZ.

(** Source for [pure_combination_mu]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pure_combination_mu x : pure_combination (mu x).
Proof. by exists [:: (1, x)]; rewrite big_seq1 scale1r. Qed.

(** Source for [tensor_family_span]: Federer (1969), 1.1.1, p. 9, universal
    property and quotient existence proof. In words: The tensor product
    represents multilinear maps; its construction is the quotient of the
    finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Theorem tensor_family_span t : pure_combination t.
Proof.
pose p : {linear T -> module_quotient pure_subspace} :=
  GRing.Linear.clone _ _ _ _ (quotient_projection pure_subspace) _.
pose z : {linear T -> module_quotient pure_subspace} :=
  GRing.Linear.clone _ _ _ _ (\0 : T -> module_quotient pure_subspace) _.
have e := tensor_family_ext H p z.
have /quotient_projection_eq : quotient_projection pure_subspace t =
    quotient_projection pure_subspace 0.
  rewrite linear0; apply: e => x /=.
  rewrite -(linear0 (quotient_projection pure_subspace)).
  apply/quotient_projection_eq; rewrite subr0.
  exact: pure_combination_mu.
by rewrite subr0.
Qed.

(** Source for [tensor_family_induction]: Federer (1969), 1.1.1, p. 9,
    universal property and quotient existence proof. In words: The tensor
    product represents multilinear maps; its construction is the quotient of
    the finitely supported free space by the multilinearity relations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma tensor_family_induction (P : T -> Prop)
    (h0 : P 0) (hadd : forall t u, P t -> P u -> P (t + u))
    (hscale : forall a t, P t -> P (a *: t))
    (hpure : forall x, P (mu x)) :
  forall t, P t.
Proof.
move=> t; have [s ->] := tensor_family_span t.
by apply: big_ind => // p _; exact: hscale (hpure p.2).
Qed.
End Spanning.
