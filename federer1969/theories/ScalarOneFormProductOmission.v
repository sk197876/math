(** Federer (1969), 4.1.6, pp. 352–353: the
    product of a scalar one-covector and a vector-valued
    form has the original signed omission values.
    This uses the existing contraction identity of
    1.5.3, retaining arbitrary coefficient spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Bilinear Alternating OneFormLinear
  ScalarTensorContraction MixedAlternatingProduct MixedScalarContraction
  ScalarCovectorWordContraction ExteriorDifferentialUP ExteriorOmittedTupleValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_one_form_product_omission]: the
    original DX_j wedge D_j phi evaluation which
    yields the defining signed formula, Federer
    4.1.6, pp. 352–353. *)
Theorem scalar_one_form_product_omission (K:fieldType) (h2:(1+1:K)!=0)
    (V W:lmodType K) m (a:A_m V K^o 1) (b:A_m V W m) (t:m.+1.-tuple V):
  mixed_form_product h2 (@scalar_action_bilinear K W) a b t=
    \sum_(i:'I_m.+1) (-1:K)^+(val i) *:
      (one_hom a (tnth t i) *:b (exterior_omitted_tuple t i)).
Proof.
rewrite mixed_scalar_form_product_contraction scalar_covector_word_contraction size_tuple linear_sum.
apply:eq_bigr=>i _.
have hEval:form_homogeneous b (exterior_word (take i t++drop i.+1 t))=
    b (exterior_omitted_tuple t i).
  by rewrite -exterior_omitted_tuple_values form_homogeneousE form_extensionE form_wordsE.
rewrite linearZ.
change (((-1:K)^+(val i)*one_hom a (nth 0 t i))*:
  form_homogeneous b (exterior_word (take i t++drop i.+1 t))=
  (-1:K)^+(val i)*:(one_hom a (tnth t i)*:b (exterior_omitted_tuple t i))).
by rewrite hEval -(tnth_nth 0) scalerA.
Qed.
