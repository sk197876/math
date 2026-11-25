(** Federer (1969), 3.2.46, p. 281: compare a frozen
    tensor integral with the Euclidean length of L composed
    with C and then with the distance between its endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  RealMetricBackground LipschitzUP PositiveSymmetricNormFactor
  RiemannianCurveCost FrozenTensorCurveLength CurveVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [frozen_tensor_curve_endpoint_bound]: the
    endpoint lower bound for each frozen curve integral in
    Federer 3.2.46, p. 281, from the true integral-length
    equality and the two-point variation partition. Equal
    interval endpoints are included. *)
Lemma frozen_tensor_curve_endpoint_bound (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n})
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) ell a b :
  is_positive_symmetric_norm_factor hB L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C ell ->
  a <= b ->
  ((inner_norm (@euclidean_inner_productP R n) (L (C b-C a)))%:E <=
    riemannian_curve_cost (fun _=>B) C a b)%E.
Proof.
move=> hL hC hab; case: (ltP a b)=> hStrict.
- rewrite (frozen_tensor_curve_cost_variation hL hC hStrict) linearB.
  have h := @curve_variation_ge_distance R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    (fun t=>L (C t)) a b hab.
  rewrite inner_metric_distanceE in h.
  rewrite (real_seminorm_subtract (inner_norm_real_norm (@euclidean_inner_productP R n)).1
    (L (C b)) (L (C a))); exact: h.
- have hEq : a = b by apply/eqP; rewrite eq_le hab hStrict.
  rewrite -hEq subrr linear0 inner_norm0.
  exact: riemannian_curve_cost_nonnegative.
Qed.
