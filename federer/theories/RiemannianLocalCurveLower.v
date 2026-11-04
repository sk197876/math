(** Federer (1969), 3.2.46, p. 281: the lower local
    distance comparison must cover every competing curve,
    including curves leaving the comparison ellipsoid.
    Both endpoint collars are retained in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  RealMetricBackground LipschitzUP PositiveSymmetricNormFactor
  RiemannianTensorUP RiemannianCurveCost RiemannianCurveFrozenLower
  RiemannianCurveSubinterval RiemannianCurveIntegralSplitting
  RiemannianCurveCollarBudget RiemannianTwoCollars FrozenLinearCurveProfile
  ContinuousTwoLevelCrossings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_global_local_curve_lower]: every
    genuine competing curve between points in the half ellipsoid
    has the required lower length bound in Federer 3.2.46,
    p. 281. A curve that escapes contributes its first-exit
    and last-return collars; the middle cost remains nonnegative.
    Global Lipschitz regularity here is only for a representative
    and is removed by the retraction theorem downstream. *)
Lemma riemannian_global_local_curve_lower (R : realType) n A g B
    (hg : @is_continuous_riemannian_tensor R n A g)
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) o x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b ell c d :
  is_positive_symmetric_norm_factor hB L ->
  is_riemannian_admissible_curve A x y C a b ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C ell ->
  0 < c -> 0 < d ->
  (forall z, inner_norm hB (z-o) <= d -> forall v,
    inner_norm hB v <= c*riemannian_tensor_speed g z v) ->
  inner_norm hB (x-o) <= d/2 -> inner_norm hB (y-o) <= d/2 ->
  ((inner_norm hB ((y-x)%R))%:E <= c%:E*riemannian_curve_cost g C a b)%E.
Proof.
move=> hL hC hGlobal hc hd hControl hx hy.
pose f := fun t : real_line_metric R=>inner_norm hB (C t-o).
case: (pselect (forall t : R, a <= t <= b -> f t <= d))=> hStay.
- have hBound t ht v := hControl (C t) (hStay t ht) v.
  have hLower := @riemannian_curve_frozen_endpoint_lower R n A g B hg hB L x y C a b c
    hL hC hc hBound.
  by rewrite (positive_norm_factor_norm hL) in hLower.
- have [q [hq hEscape]] : exists q : R, a <= q <= b /\ d < f q.
    apply: contrapT=> hNo; apply: hStay=> t ht.
    rewrite leNgt; apply/negP=> hOutside.
    apply: hNo; exists t; exact: conj ht hOutside.
  have /andP [haq hqb] := hq.
  have hCa : C a = x := hC.2.2.2.1.
  have hCb : C b = y := hC.2.2.2.2.
  have hf : continuous (f : real_line_metric R -> real_line_metric R).
    have he : f = (fun t : real_line_metric R=>
        inner_norm (@euclidean_inner_productP R n) (L (C t-o))).
      apply: funext=> t; exact: esym (positive_norm_factor_norm hL (C t-o)).
    rewrite he; exact (@frozen_linear_curve_profile_continuous R n L o C ell hGlobal).
  have hHalf : d/2 < d by lra.
  have hStart : f a < d by rewrite /f hCa; exact: le_lt_trans hx hHalf.
  have hEnd : f b < d by rewrite /f hCb; exact: le_lt_trans hy hHalf.
  have [u [v [hu [hv [hUValue [hVValue [hPrefix hSuffix]]]]]]] :=
    @continuous_two_level_crossings R f a b q d hf hq hStart hEscape hEnd.
  have /andP [hau huq] := hu.
  have /andP [hqv hvb] := hv.
  have hub : u <= b := le_trans (ltW huq) hqb.
  have hav : a <= v := le_trans haq (ltW hqv).
  have huv : u <= v := ltW (lt_trans huq hqv).
  have hLeft := riemannian_admissible_curve_subinterval hC (lexx a) (ltW hau) hub.
  have hRight := riemannian_admissible_curve_subinterval hC hav (ltW hvb) (lexx b).
  have hLeftBound t ht w := hControl (C t) (hPrefix t ht) w.
  have hRightBound t ht w := hControl (C t) (hSuffix t ht) w.
  have hLeftLower := @riemannian_curve_frozen_endpoint_lower R n A g B hg hB L
    (C a) (C u) C a u c hL hLeft hc hLeftBound.
  have hRightLower := @riemannian_curve_frozen_endpoint_lower R n A g B hg hB L
    (C v) (C b) C v b c hL hRight hc hRightBound.
  have hWholeE := riemannian_admissible_curve_cost_finite_value hg hC.
  have hLeftE := riemannian_admissible_curve_cost_finite_value hg hLeft.
  have hRightE := riemannian_admissible_curve_cost_finite_value hg hRight.
  rewrite (positive_norm_factor_norm hL) hCa hLeftE -EFinM lee_fin in hLeftLower.
  rewrite (positive_norm_factor_norm hL) hCb hRightE -EFinM lee_fin in hRightLower.
  have hBudget := riemannian_curve_two_collar_budget hg hC (ltW hau) huv (ltW hvb).
  rewrite hLeftE hRightE hWholeE -EFinD lee_fin in hBudget.
  have hSum := lerD hLeftLower hRightLower.
  rewrite -mulrDr in hSum.
  have hCollar := @norm_two_collar_lower_bound R (R_n R n) (inner_norm hB)
    (inner_norm_real_norm hB) o x y (C u) (C v) d hx hy hUValue hVValue.
  have hFinal := le_trans hCollar (le_trans hSum (ler_wpM2l (ltW hc) hBudget)).
  rewrite (real_seminorm_subtract (inner_norm_real_norm hB).1 x y) in hFinal.
  rewrite hWholeE -EFinM lee_fin; exact: hFinal.
Qed.
