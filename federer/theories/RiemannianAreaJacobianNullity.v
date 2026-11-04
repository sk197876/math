(** Federer (1969), 3.2.46, p. 282: changing the
    positive source and target inner products preserves
    the singular area rank alternative. This supporting
    exact zero criterion retains all dimensions and ranks. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  EuclideanLinearJacobian RiemannianLinearJacobian RiemannianJacobianRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_area_jacobian_zero_iff]: actual
    Riemannian area Jacobian zero is equivalent to actual
    Euclidean area Jacobian zero, supporting the singular
    set reduction of 3.2.46, p. 282. Both are
    computed from the same original linear map; no rank
    or positivity premise is added. *)
Lemma riemannian_area_jacobian_zero_iff (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B) (hC : @is_inner_product R (R_n R n) C)
    (D : Hom (R_n R m) (R_n R n)) :
  riemannian_linear_jacobian hB hC m D=0 <-> euclidean_linear_jacobian m D=0.
Proof.
split=> hZero; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite leNgt; apply/negP=> hPositive.
  have hInj := (euclidean_linear_jacobian_top_positive D).1 hPositive.
  have hRPositive := (@riemannian_area_jacobian_positive_iff_injective R m n B C hB hC D).2 hInj.
  by rewrite hZero ltxx in hRPositive.
- exact: euclidean_linear_jacobian_nonnegative.
- rewrite leNgt; apply/negP=> hPositive.
  have hInj := (@riemannian_area_jacobian_positive_iff_injective R m n B C hB hC D).1 hPositive.
  have hEPositive := (euclidean_linear_jacobian_top_positive D).2 hInj.
  by rewrite hZero ltxx in hEPositive.
- exact: riemannian_linear_jacobian_nonnegative.
Qed.
