(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Two applications of the tensor universal property extend a quadrilinear map. *)
Section DoubleExtension.
Variable K : fieldType.
Variables A B C D Z : lmodType K.
Variable h : A -> B -> C -> D -> Z.
Hypothesis hab : forall c d, bilinear (fun a b => h a b c d).
Hypothesis hcd : forall a b, bilinear (h a b).
(** Source for [tensor_extend_left]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_extend_left c d := tensor_lift (hab c d).
HB.instance Definition _ c d := GRing.Linear.copy (tensor_extend_left c d) (tensor_lift (hab c d)).
(** Source for [tensor_extend_leftE]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_extend_leftE a b c d : tensor_extend_left c d (tensor_inj a b) = h a b c d.
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_extend_left_bilinear]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_extend_left_bilinear x : bilinear (fun c d => tensor_extend_left c d x).
Proof.
elim/tensor_induction: x => [|x y [hx1 hx2] [hy1 hy2]|a x [hx1 hx2]|a b]; split.
- by move=> d a c c'; rewrite !linear0 ?scaler0 ?add0r.
- by move=> c a d d'; rewrite !linear0 ?scaler0 ?add0r.
- by move=> d a c c'; rewrite !linearD /= hx1 hy1 ?scalerDr addrACA.
- by move=> c a d d'; rewrite !linearD /= hx2 hy2 ?scalerDr addrACA.
- by move=> d b c c'; rewrite !linearZ /= hx1 ?scalerDr !scalerA (mulrC a b).
- by move=> c b d d'; rewrite !linearZ /= hx2 ?scalerDr !scalerA (mulrC a b).
- by move=> d e c c'; rewrite !tensor_extend_leftE (proj1 (hcd a b) d).
- by move=> c e d d'; rewrite !tensor_extend_leftE (proj2 (hcd a b) c).
Qed.
(** Source for [tensor_bilinear_extension]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_bilinear_extension x := tensor_lift (tensor_extend_left_bilinear x).
HB.instance Definition _ x := GRing.Linear.copy (tensor_bilinear_extension x)
  (tensor_lift (tensor_extend_left_bilinear x)).
(** Source for [tensor_bilinear_extension_r]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_bilinear_extension_r x c d :
  tensor_bilinear_extension x (tensor_inj c d) = tensor_extend_left c d x.
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_bilinear_extensionE]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_bilinear_extensionE a b c d :
  tensor_bilinear_extension (tensor_inj a b) (tensor_inj c d) = h a b c d.
Proof. by rewrite tensor_bilinear_extension_r tensor_extend_leftE. Qed.
(** Source for [tensor_bilinear_extension_bilinear]: Federer (1969), 1.1.1,
    p. 9, universal-property paragraph and the following uniqueness
    assertion. In words: Every multilinear map factors uniquely through the
    tensor product by a linear map; this characterises the tensor product up
    to a compatible linear isomorphism. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma tensor_bilinear_extension_bilinear : bilinear tensor_bilinear_extension.
Proof.
split; last by move=> x; exact: linearP.
move=> y a x x'; elim/tensor_induction: y => [|y y' hy hy'|b y hy|c d].
- by rewrite !linear0 /= ?scaler0 ?add0r.
- by rewrite !linearD /= hy hy' ?scalerDr addrACA.
- by rewrite !linearZ /= hy ?scalerDr !scalerA (mulrC b a).
by rewrite !tensor_bilinear_extension_r /tensor_extend_left linearP.
Qed.
End DoubleExtension.
