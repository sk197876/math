(** Federer (1969), 3.2.46, p. 282: actual
    Jacobians under simultaneous source and target metric
    changes. Independent vector-norm bounds control every
    exterior degree through the proved operator-norm laws,
    including critical rank and the empty exterior product. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps InnerProductUP InnerNorm
  RiemannianLinearJacobian ExteriorSourceMetricComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_jacobian_two_metric_bound]:
    independent source and target comparisons give
    J_{B,C}(F)<=delta^k lambda^k J_{B',C'}(F), supporting
    the frozen-coordinate coarea argument of 3.2.46,
    p. 282. Every original linear map and degree remains. *)
Lemma riemannian_jacobian_two_metric_bound (R : realType) m n B B' C C'
    (hB : @is_inner_product R (R_n R m) B) (hB' : @is_inner_product R (R_n R m) B')
    (hC : @is_inner_product R (R_n R n) C) (hC' : @is_inner_product R (R_n R n) C')
    (lambda delta : R) k (F : Hom (R_n R m) (R_n R n)) :
  0<=lambda -> 0<=delta ->
  (forall v, inner_norm hB' v<=lambda*inner_norm hB v) ->
  (forall v, inner_norm hC v<=delta*inner_norm hC' v) ->
  riemannian_linear_jacobian hB hC k F<=
    delta^+k*(lambda^+k*riemannian_linear_jacobian hB' hC' k F).
Proof.
move=> hLambda hDelta hSource hTarget.
exact (@exterior_operator_two_metric_comparison R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) B B' C C' hB hB' hC hC'
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (hom_as_linear F)
  lambda delta k _ _ hLambda hDelta hSource hTarget
  (riemannian_linear_jacobian_laws hB hC k F)
  (riemannian_linear_jacobian_laws hB' hC' k F)).
Qed.

(** Source for [riemannian_jacobian_symmetric_metric_bounds]:
    two-sided lambda comparisons on both original metrics
    give both lambda^(2k) Jacobian comparisons in
    3.2.46, p. 282. Nonnegative lambda and all
    natural degrees, including zero, are retained. *)
Theorem riemannian_jacobian_symmetric_metric_bounds (R : realType) m n B B' C C'
    (hB : @is_inner_product R (R_n R m) B) (hB' : @is_inner_product R (R_n R m) B')
    (hC : @is_inner_product R (R_n R n) C) (hC' : @is_inner_product R (R_n R n) C')
    (lambda : R) k (F : Hom (R_n R m) (R_n R n)) :
  0<=lambda ->
  (forall v, inner_norm hB' v<=lambda*inner_norm hB v /\ inner_norm hB v<=lambda*inner_norm hB' v) ->
  (forall v, inner_norm hC v<=lambda*inner_norm hC' v /\ inner_norm hC' v<=lambda*inner_norm hC v) ->
  riemannian_linear_jacobian hB hC k F<=lambda^+(k+k)*riemannian_linear_jacobian hB' hC' k F /\
  riemannian_linear_jacobian hB' hC' k F<=lambda^+(k+k)*riemannian_linear_jacobian hB hC k F.
Proof.
move=> hLambda hSource hTarget; split.
- have hEstimate := @riemannian_jacobian_two_metric_bound R m n B B' C C' hB hB' hC hC'
    lambda lambda k F hLambda hLambda (fun v=>(hSource v).1) (fun v=>(hTarget v).1).
  by rewrite mulrA -exprD in hEstimate.
- have hEstimate := @riemannian_jacobian_two_metric_bound R m n B' B C' C hB' hB hC' hC
    lambda lambda k F hLambda hLambda (fun v=>(hSource v).2) (fun v=>(hTarget v).2).
  by rewrite mulrA -exprD in hEstimate.
Qed.
