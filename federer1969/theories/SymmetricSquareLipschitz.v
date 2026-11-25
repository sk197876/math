(** Federer (1969), 3.2.28(4), p. 267:
    the distance identity for T(x)=x^2/2 makes
    its restriction to any unit-sphere subset Lipschitz,
    as required by the area formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import InnerProductUP InnerNorm InnerMetric SymmetricGrading InnerSymmetricPositivity
  SymmetricSquareGeometry SymmetricSquareLocalLifts LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_projective_square_unit_lipschitz]:
    the actual square map has Lipschitz bound one
    on every subset of the unit sphere, Federer
    3.2.28(4), p. 267. The difference of
    the squared distance bounds is (1-x.y)^2,
    so no compactness or finite-dimensional hypothesis
    is needed for this estimate. *)
Theorem inner_projective_square_unit_lipschitz (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V):
  (forall x,A x ->inner_norm hB x= 1) ->
  @is_metric_lipschitz_bound R (inner_metric_space hB)
    (inner_metric_space (@symmetric_inner_productP R V B hB 2)) A
    (@inner_projective_square R V) 1.
Proof.
move=>hA; split; first exact:ler01.
move=>x y hx hy; rewrite !inner_metric_distanceE mul1r.
rewrite -(ler_sqr (inner_norm_nonnegative (@symmetric_inner_productP R V B hB 2) _)
  (inner_norm_nonnegative hB _))
  (@inner_projective_square_unit_distance R V B hB x y (hA x hx) (hA y hy))
  (@inner_unit_difference_square R V B hB x y (hA x hx) (hA y hy)).
have hSquare:=sqr_ge0 (1-B x y); nra.
Qed.
