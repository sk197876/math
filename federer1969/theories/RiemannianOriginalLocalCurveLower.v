(** Federer (1969), 3.2.46, p. 281: every original
    interval-only admissible curve satisfies the local lower
    length comparison, including curves leaving the ellipsoid.
    A constant extension is used only as a proved representative. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric RealMetricBackground
  LipschitzUP LipschitzIntervalRetraction StieltjesSubstitution
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveRetraction RiemannianLocalCurveLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_original_local_curve_lower]:
    the local lower curve estimate used in Federer 3.2.46,
    p. 281, under exactly the book's interval-only admissibility.
    No containment of the competing curve in the comparison
    neighbourhood and no global Lipschitz premise is added. *)
Lemma riemannian_original_local_curve_lower (R : realType) n A g B
    (hg : @is_continuous_riemannian_tensor R n A g)
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) o x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b c d :
  is_positive_symmetric_norm_factor hB L ->
  is_riemannian_admissible_curve A x y C a b -> 0 < c -> 0 < d ->
  (forall z, inner_norm hB (z-o) <= d -> forall v,
    inner_norm hB v <= c*riemannian_tensor_speed g z v) ->
  inner_norm hB (x-o) <= d/2 -> inner_norm hB (y-o) <= d/2 ->
  ((inner_norm hB ((y-x)%R))%:E <= c%:E*riemannian_curve_cost g C a b)%E.
Proof.
move=> hL hC hc hd hControl hx hy.
have [ell [hEll hBound]] := hC.2.1.
have hGlobal := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b ell hC.1 hBound.
have hD := riemannian_retracted_curve_admissible hC.
have hLower := @riemannian_global_local_curve_lower R n A g B hg hB L o x y
  (fun t=>C (segment_retraction a b t)) a b ell c d
  hL hD hGlobal hc hd hControl hx hy.
by rewrite -(riemannian_retracted_curve_cost hg hC) in hLower.
Qed.
