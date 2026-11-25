(** Federer (1969), 3.1.11, p. 222,
    and 3.1.13, p. 225:
    finite norm bounds for the symmetric products
    in the higher Leibniz formula, using the
    estimate of 1.10.5, p. 47. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import TensorUP Hom BoundedHom Bilinear RealNormUP SymmetricAlgebra SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFormProduct SymmetricOperatorNormUP SymmetricOperatorNorm SymmetricOperatorProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteBounds.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable mu : Y->Y->Y.
Hypothesis hmu : bilinear mu.
Hypothesis hM : forall x y, NY (mu x y)<=NY x*NY y.

(** Source for [symmetric_product_finite_operator_bound]:
    the finite version of the binomial
    product estimate of 1.10.5, p. 47,
    applied to the Leibniz terms in
    Federer 3.1.11, p. 222. *)
Lemma symmetric_product_finite_operator_bound p q
    (phi : S_m X Y p) (psi : S_m X Y q) F G :
  (symmetric_operator_norm hNX.1 NY phi<=F%:E)%E ->
  (symmetric_operator_norm hNX.1 NY psi<=G%:E)%E ->
  (symmetric_operator_norm hNX.1 NY (sform_product hmu phi psi)
    <=(('C(p+q,p))%:R*(F*G))%:E)%E.
Proof.
move=>hF hG.
have hphi := symmetric_operator_norm_ge_zero hNX.1 hNY.1 phi.
have hpsi := symmetric_operator_norm_ge_zero hNX.1 hNY.1 psi.
have hp := symmetric_operator_product_bound hNX.1 hNY.1 hmu hM phi psi.
apply: le_trans hp _.
have hmul : (symmetric_operator_norm hNX.1 NY phi*
    symmetric_operator_norm hNX.1 NY psi<=F%:E*G%:E)%E.
  exact: lee_pmul hphi hpsi hF hG.
rewrite EFinM EFinM; apply: lee_wpmul2l _ hmul.
by rewrite lee_fin ler0n.
Qed.

(** Source for [symmetric_product_included_unit_bound]:
    evaluating one homogeneous product on
    a unit tuple gives the same
    binomial bound, supporting the derivative
    estimates in Federer 3.1.13,
    p. 225. The equality of
    total degrees is explicit. *)
Lemma symmetric_product_included_unit_bound p q n
    (phi : S_m X Y p) (psi : S_m X Y q) F G
    (t : n.-tuple X) :
  (p+q=n)%N ->
  (symmetric_operator_norm hNX.1 NY phi<=F%:E)%E ->
  (symmetric_operator_norm hNX.1 NY psi<=G%:E)%E ->
  symmetric_form_unit_tuple NX t ->
  NY (symmetric_forms_product hmu (sform_include phi) (sform_include psi)
    (symmetric_word t))<=('C(n,p))%:R*(F*G).
Proof.
move=>hdeg hF hG ht; subst n.
rewrite -sform_product_include sform_includeE sform_extensionE sform_wordsE.
have hu := symmetric_operator_norm_upper hNX.1 NY (sform_product hmu phi psi) ht.
have hb := symmetric_product_finite_operator_bound hF hG.
have hh := le_trans hu hb; by move:hh; rewrite lee_fin.
Qed.
End FiniteBounds.
