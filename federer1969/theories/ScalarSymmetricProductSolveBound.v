(** Federer (1969), 3.1.13, p. 225:
    isolate the highest derivative in sigma*v=u
    and use sigma>=1. Lower-order derivatives
    alone appear on the right of the estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
From Federer Require Import BoundedHom Hom ScalarCoefficients RealNormUP SymmetricAlgebra
  SymmetricForms SymmetricFormZero SymmetricFormSum SymmetricFormProduct
  SymmetricOperatorNormUP SymmetricOperatorNorm SymmetricProductFiniteBounds
  ScalarSymmetricProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_symmetric_product_solve_bound]:
    the inductive derivative estimate for the
    normalized partition in Federer 3.1.13,
    p. 225, derived from the
    general Leibniz formula on p. 222.
    The upper bound contains no norm of
    the unknown highest derivative. *)
Theorem scalar_symmetric_product_solve_bound (R : realType)
    (X : lmodType R) (NX : X->R) (hNX : is_real_norm NX)
    (phi psi : forall i, S_m X R^o i) n
    (eta : S_m X R^o n) (c H : R) (F G : nat->R) :
  1<=c ->
  phi 0%N=zero_sform X (c : R^o) ->
  sform_include eta=\sum_(j<n.+1)
    symmetric_forms_product (ScalarCoefficients.scalar_bilinear R)
      (sform_include (phi (n-j)%N)) (sform_include (psi j)) ->
  (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) eta<=H%:E)%E ->
  (forall j, (j<=n)%N ->
    (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) (phi j)<=(F j)%:E)%E) ->
  (forall j, (j<n)%N ->
    (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) (psi j)<=(G j)%:E)%E) ->
  (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) (psi n)<=
    (H+\sum_(j<n) ('C(n,n-j))%:R*(F (n-j)%N*G j))%:E)%E.
Proof.
move=>hc hphi0 hprod hH hF hG.
have hc0 : 0<=c := le_trans ler01 hc.
rewrite big_ord_recr /= subnn hphi0 scalar_symmetric_coefficient_product in hprod.
apply: (symmetric_operator_norm_bound hNX.1 (fun t : R^o=>`|t|%R) (psi n) _).2=>t ht.
have he := congr1 (fun a : S_star X R^o=>a (symmetric_word t)) hprod.
cbv beta in he.
rewrite hom_finite_addE hom_finite_scaleE hom_finite_sumE in he.
have heta : sform_include eta (symmetric_word t)=eta t.
  by rewrite -sform_componentE sform_includeK.
have hpsi : sform_include (psi n) (symmetric_word t)=psi n t.
  by rewrite -sform_componentE sform_includeK.
rewrite heta hpsi in he.
pose r := \sum_(j<n)
  symmetric_forms_product (ScalarCoefficients.scalar_bilinear R)
    (sform_include (phi (n-j)%N)) (sform_include (psi j)) (symmetric_word t).
have hsolve : c*(psi n t)=eta t-r.
  change (eta t=r+c*(psi n t)) in he; by rewrite he addrAC subrr add0r.
have hlower : `|psi n t|<=c*`|psi n t|.
  have hh := ler_wpM2r (normr_ge0 (psi n t)) hc; by rewrite mul1r in hh.
have hstep : c*`|psi n t|<=`|eta t|+\sum_(j<n) `|
  symmetric_forms_product (ScalarCoefficients.scalar_bilinear R)
    (sform_include (phi (n-j)%N)) (sform_include (psi j)) (symmetric_word t)|.
  rewrite -(ger0_norm hc0) -normrM hsolve.
  apply: (le_trans (ler_normB _ _)).
  apply: lerD; first exact: lexx.
  exact: ler_norm_sum.
have hEta := (symmetric_operator_norm_bound hNX.1 (fun t : R^o=>`|t|%R) eta H).1 hH t ht.
have hrest : (\sum_(j<n) `|
    symmetric_forms_product (ScalarCoefficients.scalar_bilinear R)
      (sform_include (phi (n-j)%N)) (sform_include (psi j)) (symmetric_word t)|)
    <=\sum_(j<n) ('C(n,n-j))%:R*(F (n-j)%N*G j).
  apply: ler_sum=>j _.
  have hjn : (j<=n)%N := ltnW (ltn_ord j).
  have hsub (x y : R^o) : `|x*y|<=`|x|*`|y| by rewrite normrM.
  exact: (symmetric_product_included_unit_bound (@scalar_absolute_value_norm R)
    (ScalarCoefficients.scalar_bilinear R) hsub
    (subnK hjn) (hF _ (leq_subr j n)) (hG _ (ltn_ord j)) ht).
exact: (le_trans hlower (le_trans hstep (lerD hEta hrest))).
Qed.
