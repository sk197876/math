(** Federer (1969), 4.1.6, pp. 351–353: alternating
    multiplication with a scalar and normed vector
    coefficients. The arbitrary bilinear coefficient
    pairing is the already specified mixed tensor
    pairing of 1.10.2; the original exterior diagonal
    and homogeneous-form isomorphism are reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP Bilinear Alternating AlternatingIsomorphism
  AlternatingWords AlternatingProduct FiniteExteriorPowers GradedComponents
  MixedTensorPairing MixedHomogeneousConvolution HomogeneousHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section MixedAlternatingProduct.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V W1 W2 W3:lmodType K.
Variable B:W1->W2->W3.
Hypothesis hB:bilinear B.

(** Source for [mixed_form_product]: the original
    alternating product through a coefficient pairing,
    used for DX_j wedge D_j phi in Federer 4.1.6,
    p. 353. Degree is added by the original exterior
    diagonal, not by a new shuffle construction. *)
Definition mixed_form_product p q (a:A_m V W1 p) (b:A_m V W2 q):A_m V W3 (p+q):=
  homogeneous_form (mixed_homogeneous_convolution hB (@Psi_graded K h2 V)
    (form_homogeneous a) (form_homogeneous b)).

(** Source for [mixed_form_product_tuple]: its original
    tensor-composite evaluation, supporting the derivative
    formula in Federer 4.1.6, pp. 352–353. *)
Lemma mixed_form_product_tuple p q (a:A_m V W1 p) (b:A_m V W2 q) (t:(p+q).-tuple V):
  mixed_form_product a b t=
    mixed_paired_tensor hB (form_homogeneous a) (form_homogeneous b) (Psi h2 V (exterior_word t)).
Proof. by []. Qed.

(** Source for [mixed_form_product_bilinear]: the mixed
    coefficient operation is bilinear, as required for
    the original exterior derivative construction,
    Federer 4.1.6, pp. 352–353. *)
Lemma mixed_form_product_bilinear p q:bilinear (@mixed_form_product p q).
Proof.
split.
- move=>b c a a'; apply:form_ext=>t.
  rewrite form_addE form_scaleE !mixed_form_product_tuple (linearP (@form_homogeneous K V W1 p)).
  exact:((mixed_paired_tensor_parameter_bilinear hB (Psi h2 V (exterior_word t))).1).
- move=>a c b b'; apply:form_ext=>t.
  rewrite form_addE form_scaleE !mixed_form_product_tuple (linearP (@form_homogeneous K V W2 q)).
  exact:((mixed_paired_tensor_parameter_bilinear hB (Psi h2 V (exterior_word t))).2).
Qed.
End MixedAlternatingProduct.
