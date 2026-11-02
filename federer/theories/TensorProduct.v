(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP TensorSealed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.1: the tensor product V ⊗ W used in the sequel. It is the
    sealed tensor product of TensorSealed.v; everything below follows from
    its universal property. *)
Section TensorProduct.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [tensor_space]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_space : lmodType K := tensor V W.
(** Source for [tensor_inj]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Definition or construction used to formalise this passage. *)
Definition tensor_inj (v : V) (w : W) : tensor_space := tensor_mul v w.

(** Source for [tensor_exists]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem tensor_exists : is_tensor_product tensor_inj.
Proof. exact: tensorP. Qed.

(** Source for [tensor_inj_bilinear]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_inj_bilinear : bilinear tensor_inj.
Proof. exact: tensor_bilinear tensor_exists. Qed.

(** Source for [tensor_inj_addl]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_inj_addl v v' w :
  tensor_inj (v + v') w = tensor_inj v w + tensor_inj v' w.
Proof.
have [h _] := tensor_inj_bilinear.
by have := h w 1 v v'; rewrite !scale1r.
Qed.
(** Source for [tensor_inj_addr]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_inj_addr v w w' :
  tensor_inj v (w + w') = tensor_inj v w + tensor_inj v w'.
Proof.
have [_ h] := tensor_inj_bilinear.
by have := h v 1 w w'; rewrite !scale1r.
Qed.
(** Source for [tensor_inj_scalel]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_inj_scalel a v w :
  tensor_inj (a *: v) w = a *: tensor_inj v w.
Proof. by have [h _] := tensor_inj_bilinear; have := GRing.scalable_linear (h w) a v. Qed.
(** Source for [tensor_inj_scaler]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_inj_scaler a v w :
  tensor_inj v (a *: w) = a *: tensor_inj v w.
Proof. by have [_ h] := tensor_inj_bilinear; have := GRing.scalable_linear (h v) a w. Qed.

Section Lift.
Variable Z : lmodType K.
Variable beta : V -> W -> Z.
Hypothesis beta_bilinear : bilinear beta.

(** Source for [tensor_lift_sig]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_lift_sig := cid (tensor_universal tensor_exists beta_bilinear).

(** Source for [tensor_lift]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_lift : tensor_space -> Z := proj1_sig tensor_lift_sig.
HB.instance Definition _ := GRing.Linear.copy tensor_lift (proj1_sig tensor_lift_sig).

(** Source for [tensor_liftE]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_liftE v w : tensor_lift (tensor_inj v w) = beta v w.
Proof. exact: (proj1 (proj2_sig tensor_lift_sig)). Qed.

(** Source for [tensor_lift_unique]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_lift_unique (g : {linear tensor_space -> Z}) :
  (forall v w, g (tensor_inj v w) = beta v w) -> forall t, g t = tensor_lift t.
Proof. exact: (proj2 (proj2_sig tensor_lift_sig)). Qed.
End Lift.
End TensorProduct.
