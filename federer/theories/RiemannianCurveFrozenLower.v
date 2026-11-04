(** Federer (1969), 3.2.46, p. 281: comparison of a
    genuine curve integral with a frozen inner-product length
    gives an endpoint lower bound. The curve need only be
    Lipschitz on its original compact interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric RealMetricBackground
  LipschitzUP LipschitzIntervalRetraction StieltjesSubstitution
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianFrozenTensor
  RiemannianCurveCost RiemannianCurveCostComparison RiemannianCurveRetraction
  FrozenTensorCurveLength FrozenTensorCurveEndpoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_curve_frozen_endpoint_lower]:
    the frozen endpoint distance is bounded by the actual
    tensor integral times its local comparison factor, as used
    in Federer 3.2.46, p. 281. No assumption that a competing
    curve stays near its endpoints is hidden in this lemma;
    the displayed comparison must hold along its whole interval. *)
Lemma riemannian_curve_frozen_endpoint_lower (R : realType) n A g B
    (hg : @is_continuous_riemannian_tensor R n A g)
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b c :
  is_positive_symmetric_norm_factor hB L ->
  is_riemannian_admissible_curve A x y C a b -> 0 < c ->
  (forall t, a <= t <= b -> forall v,
    inner_norm hB v <= c*riemannian_tensor_speed g (C t) v) ->
  ((inner_norm (@euclidean_inner_productP R n) (L (y-x)))%:E <=
    c%:E*riemannian_curve_cost g C a b)%E.
Proof.
move=> hL hC hc hBound.
have hFrozen := riemannian_frozen_tensor_laws hB (riemannian_tensor_domain_open hg).
have hCompare : (riemannian_curve_cost (fun _=>B) C a b <=
    c%:E*riemannian_curve_cost g C a b)%E.
  apply: (riemannian_curve_cost_positive_comparison hFrozen hg hC hc).
  move=> t ht v; rewrite (frozen_tensor_speed_norm hB); exact: hBound t ht v.
have [ell [hEll hCBound]] := hC.2.1.
have hGlobal := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b ell hC.1 hCBound.
have hD := riemannian_retracted_curve_admissible hC.
have hEndpoint := frozen_tensor_curve_endpoint_bound hL hGlobal hC.1.
rewrite hD.2.2.2.2 hD.2.2.2.1
  -(riemannian_retracted_curve_cost hFrozen hC) in hEndpoint.
exact: le_trans hEndpoint hCompare.
Qed.
