(** Federer (1969), 4.1.6, pp. 351–353: the
    heterogeneous coefficient pairing agrees with the
    original alternating product whenever all three
    coefficient spaces are the same. In particular,
    scalar-times-real is ordinary multiplication. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP TensorProduct Bilinear Convolution
  MixedTensorPairing Alternating AlternatingProduct ScalarCoefficients
  ScalarTensorContraction MixedAlternatingProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [mixed_same_paired_tensor]: the common
    original tensor pairing in the coefficient product,
    supporting Federer 4.1.6, p. 351. *)
Lemma mixed_same_paired_tensor (K:fieldType) (X Y W:lmodType K)
    (B:W->W->W) (hB:bilinear B) (a:Hom X W) (b:Hom Y W) (t:tensor_space X Y):
  mixed_paired_tensor hB a b t=paired_tensor hB a b t.
Proof.
apply:(tensor_ext (tensor_exists X Y) (mixed_paired_tensor hB a b) (paired_tensor hB a b)) t=>x y.
by rewrite mixed_paired_tensorE paired_tensorE.
Qed.

(** Source for [mixed_same_form_product]: the original
    alternating multiplication is retained for a common
    coefficient algebra, Federer 4.1.6,
    p. 351. *)
Theorem mixed_same_form_product (K:fieldType) (h2:(1+1:K)!=0)
    (V W:lmodType K) (B:W->W->W) (hB:bilinear B) p q (a:A_m V W p) (b:A_m V W q):
  mixed_form_product h2 hB a b=form_wedge h2 hB a b.
Proof.
apply:form_ext=>t; rewrite mixed_form_product_tuple form_wedgeE.
exact:mixed_same_paired_tensor.
Qed.

(** Source for [mixed_real_form_product]: DX_j wedge
    a real form uses the original real alternating
    algebra, Federer 4.1.6, p. 353. *)
Lemma mixed_real_form_product (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) p q (a:A_m V K^o p) (b:A_m V K^o q):
  mixed_form_product h2 (@scalar_action_bilinear K K^o) a b=
    form_wedge h2 (scalar_bilinear K) a b.
Proof.
apply:form_ext=>t; rewrite mixed_form_product_tuple form_wedgeE.
apply:(tensor_ext (tensor_exists (exterior_space V) (exterior_space V))
  (mixed_paired_tensor (@scalar_action_bilinear K K^o) (form_homogeneous a) (form_homogeneous b))
  (paired_tensor (scalar_bilinear K) (form_homogeneous a) (form_homogeneous b)))
  (Psi h2 V (exterior_word t))=>x y.
by rewrite mixed_paired_tensorE paired_tensorE.
Qed.
