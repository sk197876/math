(** Federer (1969), 3.2.46, p. 281: actual two-sided
    local comparison of rho with the frozen Euclidean metric
    |L(x-y)|. The positive factor and radius are local proved
    witnesses, and every competing curve is accounted for. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric RealMetricBackground
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianTensorLocalComparison
  RiemannianCurveCost RiemannianCurveIntegralSplitting
  RiemannianOriginalLocalCurveLower RiemannianLocalSegmentDistance
  RiemannianDistanceUP RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_local_distance_comparison]:
    lambda^{-1}|L(x-y)| <= rho(x,y) <= lambda|L(x-y)|
    for endpoints in the half ellipsoid, Federer 3.2.46,
    p. 281. All admissible curves, including escaping ones,
    enter the lower infimum bound. Domain membership, finite
    upper bound and the local factor are all proved. *)
Theorem riemannian_local_distance_comparison (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) o (ho : A o) (lambda : R) :
  1 < lambda -> exists L : {linear R_n R n -> R_n R n}, exists d : R,
    0 < d /\ is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ho) L /\
    forall x y, inner_norm (@euclidean_inner_productP R n) (L (x-o)) <= d/2 ->
      inner_norm (@euclidean_inner_productP R n) (L (y-o)) <= d/2 ->
      A x /\ A y /\
      (((lambda^-1*inner_norm (@euclidean_inner_productP R n) (L (y-x)))%R)%:E <=
        @riemannian_distance R n A g x y)%E /\
      (@riemannian_distance R n A g x y <=
        ((lambda*inner_norm (@euclidean_inner_productP R n) (L (y-x)))%R)%:E)%E.
Proof.
move=> hLambda.
have hLambda0 : 0 < lambda := lt_trans ltr01 hLambda.
have hLambdaNe : lambda != 0 := lt0r_neq0 hLambda0.
have [L [d [hd [hL hControl]]]] := riemannian_tensor_local_comparison hg ho hLambda.
exists L,d; split; first exact hd; split; first exact hL.
move=> x y hx hy.
have hHalf : d/2 <= d by lra.
have hxFull := le_trans hx hHalf.
have hyFull := le_trans hy hHalf.
have hX := (hControl x hxFull).1.
have hY := (hControl y hyFull).1.
split; first exact hX; split; first exact hY; split.
- pose hB := riemannian_tensor_inner hg ho.
  have hFrozenControl z : inner_norm hB (z-o) <= d -> forall v,
      inner_norm hB v <= lambda*riemannian_tensor_speed g z v.
    move=> hz v.
    have hzL : inner_norm (@euclidean_inner_productP R n) (L (z-o)) <= d.
      by rewrite (positive_norm_factor_norm hL).
    have hLower := (hControl z hzL).2 v.
    have hScaled := ler_wpM2l (ltW hLambda0) hLower.1.
    rewrite mulrA (mulfV hLambdaNe) mul1r (positive_norm_factor_norm hL) in hScaled.
    exact: hScaled.
  have hxB : inner_norm hB (x-o) <= d/2 by rewrite -(positive_norm_factor_norm hL).
  have hyB : inner_norm hB (y-o) <= d/2 by rewrite -(positive_norm_factor_norm hL).
  apply: (riemannian_distance_greatest (riemannian_distance_laws A g x y)).
  move=> C a b hC.
  have hLower := @riemannian_original_local_curve_lower R n A g (g o) hg hB L o x y C a b lambda d
    hL hC hLambda0 hd hFrozenControl hxB hyB.
  have hCostE := riemannian_admissible_curve_cost_finite_value hg hC.
  rewrite hCostE -EFinM lee_fin -(positive_norm_factor_norm hL) in hLower.
  have hInverse0 : 0 <= lambda^-1 by rewrite invr_ge0; exact: ltW hLambda0.
  have hScaled := ler_wpM2l hInverse0 hLower.
  rewrite mulrA (mulVf hLambdaNe) mul1r in hScaled.
  rewrite hCostE lee_fin; exact: hScaled.
- have hUpper z : inner_norm (@euclidean_inner_productP R n) (L (z-o)) <= d ->
      A z /\ forall v, riemannian_tensor_speed g z v <=
        lambda*inner_norm (@euclidean_inner_productP R n) (L v).
    move=> hz; split; first exact: (hControl z hz).1.
    by move=> v; exact: ((hControl z hz).2 v).2.
  exact (@riemannian_local_segment_distance_upper R n A g hg L o x y d lambda
    hLambda0 hUpper hxFull hyFull).
Qed.
