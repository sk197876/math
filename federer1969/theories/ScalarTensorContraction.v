(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1, the map R tensor exterior(V) -> exterior(V). *)
Section ScalarTensor.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [scalar_action_bilinear]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma scalar_action_bilinear :
  @bilinear K (GRing.Lmodule.clone K K^o _) V V (fun a v => a *: v).
Proof.
split.
- by move=> v a b c; rewrite scalerDl scalerA.
- by move=> a b v w; rewrite scalerDr !scalerA mulrC.
Qed.
(** Source for [scalar_tensor]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Definition or construction used to formalise this passage. *)
Definition scalar_tensor : {linear tensor_space K^o V -> V} :=
  tensor_lift scalar_action_bilinear.
(** Source for [scalar_tensorE]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma scalar_tensorE a v : scalar_tensor (tensor_inj a v) = a *: v.
Proof. exact: tensor_liftE. Qed.
(** Source for [scalar_tensor_inverse]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Definition or construction used to formalise this passage. *)
Definition scalar_tensor_inverse (v : V) : tensor_space K^o V := tensor_inj 1 v.
(** Source for [scalar_tensor_inverse_linear]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma scalar_tensor_inverse_linear : linear scalar_tensor_inverse.
Proof. by move=> a v w; rewrite /scalar_tensor_inverse tensor_inj_addr tensor_inj_scaler. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V (tensor_space K^o V) *:%R
  scalar_tensor_inverse scalar_tensor_inverse_linear.
(** Source for [scalar_tensor_inverseK]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma scalar_tensor_inverseK : cancel scalar_tensor_inverse scalar_tensor.
Proof. by move=> v; rewrite scalar_tensorE scale1r. Qed.
(** Source for [scalar_tensorK]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma scalar_tensorK : cancel scalar_tensor scalar_tensor_inverse.
Proof.
apply: (tensor_ext (tensor_exists K^o V)
  (linear_comp (GRing.Linear.clone _ _ _ _ scalar_tensor_inverse _) scalar_tensor)
  (linear_id (tensor_space K^o V))) => a v.
change (scalar_tensor_inverse (scalar_tensor (tensor_inj a v)) = tensor_inj a v).
rewrite scalar_tensorE /scalar_tensor_inverse tensor_inj_scaler -tensor_inj_scalel.
change (tensor_inj (a*1) v = tensor_inj a v).
by rewrite mulr1.
Qed.
End ScalarTensor.

(** Federer 1.5.1: contraction on the first tensor factor. *)
Section Contraction.
Variable K : fieldType.
Variables X Y : lmodType K.
(** Source for [contract_tensor]: Federer (1969), 1.5.1, p. 22, diagonal-map
    composite and commutative diagram. In words: Apply the diagonal,
    evaluate the first factor against the homogeneous covector, then use
    scalar multiplication on the remaining factor; the diagram proves the
    characteristic pairing identity. Definition or construction used to
    formalise this passage. *)
Definition contract_tensor (h : Hom X K^o) : {linear tensor_space X Y -> Y} :=
  linear_comp (scalar_tensor Y) (tensor_map (hom_as_linear h) (linear_id Y)).
(** Source for [contract_tensorE]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma contract_tensorE h x y : contract_tensor h (tensor_inj x y) = (h x : K) *: y.
Proof.
change (scalar_tensor Y (tensor_map (hom_as_linear h) (linear_id Y) (tensor_inj x y)) = (h x : K) *: y).
by rewrite tensor_mapE scalar_tensorE.
Qed.
(** Source for [contract_tensor_parameter_linear]: Federer (1969), 1.5.1, p.
    22, diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma contract_tensor_parameter_linear t : linear (fun h : Hom X K^o => contract_tensor h t).
Proof.
move=> c h k; elim/tensor_induction: t => [|s t hs ht|a t ht|x y].
- by rewrite !linear0 ?scaler0 ?add0r.
- by rewrite !linearD hs ht ?scalerDr addrACA.
- rewrite !(linZ (linearP (contract_tensor _))) ht scalerDr !scalerA.
  by rewrite [a*c]mulrC.
- by rewrite !contract_tensorE hom_addE hom_scaleE scalerDl scalerA.
Qed.
(** Source for [contract_tensor_pairing]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma contract_tensor_pairing (h : Hom X K^o) (k : Hom Y K^o) t :
  k (contract_tensor h t) = paired_tensor (scalar_bilinear K) h k t.
Proof.
apply: (tensor_ext (tensor_exists X Y)
  (linear_comp (hom_as_linear k) (contract_tensor h))
  (paired_tensor (scalar_bilinear K) h k)) t => x y.
change (k (contract_tensor h (tensor_inj x y)) = paired_tensor (scalar_bilinear K) h k (tensor_inj x y)).
by rewrite contract_tensorE paired_tensorE linearZ.
Qed.
(** Federer 1.5.1, the lower triangle of the displayed diagram. *)
(** Source for [scalar_tensor_natural]: Federer (1969), 1.1.2, p. 10,
    scalar-multiplication paragraph. In words: Scalar multiplication induces
    the canonical linear isomorphism from R tensor V to V, taking c tensor x
    to cx. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma scalar_tensor_natural (k : Hom Y K^o) t :
  k (scalar_tensor Y t) = scalar_tensor K^o (tensor_map (linear_id K^o) (hom_as_linear k) t).
Proof.
apply: (tensor_ext (tensor_exists K^o Y)
  (linear_comp (hom_as_linear k) (scalar_tensor Y))
  (linear_comp (scalar_tensor K^o) (tensor_map (linear_id K^o) (hom_as_linear k)))) t => a y.
change (k (scalar_tensor Y (tensor_inj a y)) = scalar_tensor K^o (tensor_map (linear_id K^o) (hom_as_linear k) (tensor_inj a y))).
by rewrite tensor_mapE !scalar_tensorE linearZ.
Qed.
(** Federer 1.5.1, the tensor square in the displayed diagram. *)
(** Source for [contraction_tensor_square]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma contraction_tensor_square (h : Hom X K^o) (k : Hom Y K^o) t :
  tensor_map (linear_id K^o) (hom_as_linear k)
    (tensor_map (hom_as_linear h) (linear_id Y) t) =
  tensor_map (hom_as_linear h) (hom_as_linear k) t.
Proof.
apply: (tensor_ext (tensor_exists X Y)
  (linear_comp (tensor_map (linear_id K^o) (hom_as_linear k))
    (tensor_map (hom_as_linear h) (linear_id Y)))
  (tensor_map (hom_as_linear h) (hom_as_linear k))) t => x y.
change (tensor_map (linear_id K^o) (hom_as_linear k)
  (tensor_map (hom_as_linear h) (linear_id Y) (tensor_inj x y)) =
  tensor_map (hom_as_linear h) (hom_as_linear k) (tensor_inj x y)).
by rewrite !tensor_mapE.
Qed.
End Contraction.
