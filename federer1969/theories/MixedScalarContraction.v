(** Federer (1969), 4.1.6, pp. 352–353: scalar
    exterior multiplication with arbitrary coefficients
    is dual to the original left contraction. The
    heterogeneous pairing follows directly from the
    already proved tensor universal property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import TensorUP TensorProduct TensorMaps Hom Bilinear
  Alternating AlternatingProduct MixedTensorPairing ScalarTensorContraction
  LeftInteriorHom MixedAlternatingProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [mixed_scalar_contract_pairing]: the
    original contraction diagram of 1.5.1, now with
    arbitrary vector coefficients, supporting the
    definition of d in Federer 4.1.6, p. 352. *)
Lemma mixed_scalar_contract_pairing (K:fieldType) (X Y W:lmodType K)
    (a:Hom X K^o) (b:Hom Y W) (t:tensor_space X Y):
  b (@contract_tensor K X Y a t)=mixed_paired_tensor (@scalar_action_bilinear K W) a b t.
Proof.
apply:(tensor_ext (tensor_exists X Y)
  (linear_comp (hom_as_linear b) (@contract_tensor K X Y a))
  (mixed_paired_tensor (@scalar_action_bilinear K W) a b)) t=>x y.
change (b (@contract_tensor K X Y a (tensor_inj x y))=
  mixed_paired_tensor (@scalar_action_bilinear K W) a b (tensor_inj x y)).
by rewrite contract_tensorE mixed_paired_tensorE linearZ.
Qed.

(** Source for [mixed_scalar_form_product_contraction]:
    scalar alternating multiplication is evaluation
    after the actual contraction, supporting the
    original coordinate formula in Federer 4.1.6,
    p. 353. *)
Theorem mixed_scalar_form_product_contraction (K:fieldType) (h2:(1+1:K)!=0)
    (V W:lmodType K) p q (a:A_m V K^o p) (b:A_m V W q) (t:(p+q).-tuple V):
  mixed_form_product h2 (@scalar_action_bilinear K W) a b t=
    form_homogeneous b (left_interior_hom h2 (exterior_word t) (form_homogeneous a)).
Proof.
rewrite mixed_form_product_tuple /left_interior_hom.
exact:esym (mixed_scalar_contract_pairing _ _ _).
Qed.
