(** Federer (1969), 3.2.46, pp. 281–282: one
    pair of local metric neighbourhoods controls every
    degree of the original linear Jacobian in both
    directions. This supports genuine coarea localization;
    no Jacobian identity or derivative field is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianLocalNormComparison
  RiemannianLinearJacobian RiemannianTwoMetricJacobianComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_local_two_metric_jacobian_bounds]:
    actual varying-metric Jacobians and their frozen values
    differ by at most lambda^(2k) near the two original
    points, supporting 3.2.46, p. 282. Every linear
    map, singular rank and natural degree is included;
    local factors and radii are proved existential witnesses. *)
Theorem riemannian_local_two_metric_jacobian_bounds (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    a (ha : A a) b (hb : B b) (lambda : R) :
  1<lambda -> exists L : {linear R_n R m -> R_n R m},
    exists M : {linear R_n R n -> R_n R n}, exists d e : R,
    0<d /\ 0<e /\
    is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ha) L /\
    is_positive_symmetric_norm_factor (riemannian_tensor_inner hh hb) M /\
    (forall x, inner_norm (@euclidean_inner_productP R m) (L (x-a))<=d -> A x) /\
    (forall y, inner_norm (@euclidean_inner_productP R n) (M (y-b))<=e -> B y) /\
    forall x (hx : A x) y (hy : B y),
      inner_norm (@euclidean_inner_productP R m) (L (x-a))<=d ->
      inner_norm (@euclidean_inner_productP R n) (M (y-b))<=e ->
      forall k (F : Hom (R_n R m) (R_n R n)),
      riemannian_linear_jacobian (riemannian_tensor_inner hg hx) (riemannian_tensor_inner hh hy) k F<=
        lambda^+(k+k)*riemannian_linear_jacobian (riemannian_tensor_inner hg ha) (riemannian_tensor_inner hh hb) k F /\
      riemannian_linear_jacobian (riemannian_tensor_inner hg ha) (riemannian_tensor_inner hh hb) k F<=
        lambda^+(k+k)*riemannian_linear_jacobian (riemannian_tensor_inner hg hx) (riemannian_tensor_inner hh hy) k F.
Proof.
move=> hLambda.
have [L [d [hd [hL hSource]]]] := @riemannian_local_frozen_norm_comparison R m A g hg a ha lambda hLambda.
have [M [e [he [hM hTarget]]]] := @riemannian_local_frozen_norm_comparison R n B h hh b hb lambda hLambda.
exists L,M,d,e; split; first exact hd; split; first exact he.
split; first exact hL; split; first exact hM; split.
- move=> x hx; exact: (hSource x hx).1.
split.
- move=> y hy; exact: (hTarget y hy).1.
move=> x hx y hy hNearSource hNearTarget k F.
exact (@riemannian_jacobian_symmetric_metric_bounds R m n (g x) (g a) (h y) (h b)
  (riemannian_tensor_inner hg hx) (riemannian_tensor_inner hg ha)
  (riemannian_tensor_inner hh hy) (riemannian_tensor_inner hh hb) lambda k F
  (ltW (lt_trans ltr01 hLambda))
  (fun v=>(hSource x hNearSource).2 hx v)
  (fun v=>conj ((hTarget y hNearTarget).2 hy v).2 ((hTarget y hNearTarget).2 hy v).1)).
Qed.
