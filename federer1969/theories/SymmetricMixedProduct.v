(** Federer (1969), 1.10.2, p. 45: the general symmetric product with a
    bilinear coefficient map W1 x W2 -> W3. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor Hom HomogeneousHom
  Convolution MixedTensorPairing MixedHomogeneousConvolution SymmetricAlgebra SymmetricGrading
  SymmetricDirectSum SymmetricDiagonal SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section MixedProduct.
Variable K : fieldType.
Variables V W1 W2 W3 : lmodType K.
Variable mu : W1 -> W2 -> W3.
Hypothesis hmu : bilinear mu.
Local Notation E := (symmetric_unital V).
Local Notation D := (symmetric_diagonal V).
Local Notation hD := (@symmetric_diagonal_graded K V).

(** Source for [sform_mixed_product]: Federer 1.10.2, p. 45,
    final displayed bilinear map. The product of a W1-valued p-form
    and a W2-valued q-form is a W3-valued (p+q)-form. *)
Definition sform_mixed_product p q (a : S_m V W1 p) (b : S_m V W2 q) : S_m V W3 (p+q) :=
  homogeneous_sform (mixed_homogeneous_convolution hmu hD
    (sform_homogeneous a) (sform_homogeneous b)).

(** Source for [sform_mixed_productE]: Federer 1.10.2, p. 45,
    the three-map composition in the final paragraph, evaluated on an
    actual tuple of vectors. *)
Lemma sform_mixed_productE p q (a : S_m V W1 p) (b : S_m V W2 q) (t : (p+q).-tuple V) :
  sform_mixed_product a b t = mixed_paired_tensor hmu
    (sform_homogeneous a) (sform_homogeneous b) (D (symmetric_word t)).
Proof. by []. Qed.

(** Source for [sform_mixed_product_bilinear]: Federer 1.10.2,
    p. 45, the word bilinear in the final assertion: the constructed
    map is linear in each form separately. *)
Theorem sform_mixed_product_bilinear p q : bilinear (@sform_mixed_product p q).
Proof.
split.
- move=> b c a a'; apply: sform_ext=> t.
  rewrite sform_addE sform_scaleE !sform_mixed_productE linearP.
  exact: (proj1 (mixed_paired_tensor_parameter_bilinear hmu _) _ c _ _).
- move=> a c b b'; apply: sform_ext=> t.
  rewrite sform_addE sform_scaleE !sform_mixed_productE linearP.
  exact: (proj2 (mixed_paired_tensor_parameter_bilinear hmu _) _ c _ _).
Qed.
End MixedProduct.

(** Source for [mixed_paired_tensor_agrees]: Federer 1.10.2,
    p. 45, final paragraph. With all coefficient spaces equal,
    the generalized tensor pairing is the ordinary coefficient pairing. *)
Lemma mixed_paired_tensor_agrees (K : fieldType) (X Y W : lmodType K)
    (mu : W -> W -> W) (hmu : bilinear mu) (a : Hom X W) (b : Hom Y W) x :
  mixed_paired_tensor hmu a b x = paired_tensor hmu a b x.
Proof.
apply: (tensor_ext (tensor_exists X Y) (mixed_paired_tensor hmu a b)
  (paired_tensor hmu a b)) x=> u v.
by rewrite mixed_paired_tensorE paired_tensorE.
Qed.

(** Source for [sform_mixed_product_agrees]: Federer 1.10.2,
    p. 45, final paragraph. The arbitrary bilinear construction
    specializes to the preceding symmetric product of coefficient forms. *)
Lemma sform_mixed_product_agrees (K : fieldType) (V W : lmodType K)
    (mu : W -> W -> W) (hmu : bilinear mu) p q
    (a : S_m V W p) (b : S_m V W q) :
  sform_mixed_product hmu a b = sform_product hmu a b.
Proof.
apply: sform_ext=> t; rewrite sform_mixed_productE sform_productE.
exact: mixed_paired_tensor_agrees.
Qed.
