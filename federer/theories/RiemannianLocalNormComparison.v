(** Federer (1969), 3.2.46, p. 281: a continuous
    positive metric form is uniformly close to its frozen
    value on a sufficiently small ellipsoid. This exposes
    both actual norm comparisons used in the area/coarea
    reductions, independently of any linear-map field. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianTensorLocalComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_local_frozen_norm_comparison]:
    both lambda comparisons between the original metric
    norm at x and its value at a, supporting the
    local-isometry procedure in 3.2.46, pp. 281–282.
    The same ellipsoid controls every vector and every
    actual membership proof; its factor remains existential. *)
Theorem riemannian_local_frozen_norm_comparison (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) a (ha : A a) (lambda : R) :
  1<lambda -> exists L : {linear R_n R n -> R_n R n}, exists d : R,
    0<d /\ is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ha) L /\
    forall x, inner_norm (@euclidean_inner_productP R n) (L (x-a))<=d ->
      A x /\ forall (hx : A x) v,
        inner_norm (riemannian_tensor_inner hg ha) v<=lambda*inner_norm (riemannian_tensor_inner hg hx) v /\
        inner_norm (riemannian_tensor_inner hg hx) v<=lambda*inner_norm (riemannian_tensor_inner hg ha) v.
Proof.
move=> hLambda.
have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
have hLambdaNonzero := lt0r_neq0 hLambda0.
have [L [d [hd [hL hControl]]]] := @riemannian_tensor_local_comparison R n A g hg a ha lambda hLambda.
exists L,d; split; first exact hd; split; first exact hL.
move=> x hNear; split; first exact: (hControl x hNear).1.
move=> hx v.
have hVector := (hControl x hNear).2 v.
rewrite (riemannian_tensor_speed_inner_norm hg hx) (positive_norm_factor_norm hL) in hVector.
split; last exact: hVector.2.
have hScaled := ler_wpM2l (ltW hLambda0) hVector.1.
by rewrite mulrA (mulfV hLambdaNonzero) mul1r in hScaled.
Qed.
