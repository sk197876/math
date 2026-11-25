(** Federer (1969), 3.2.46, p. 281: leaving a
    local comparison neighbourhood costs a positive amount
    of length. This supports global separation and the
    equality of the metric and original chart topologies. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RealMetricBackground LipschitzUP LipschitzIntervalRetraction
  StieltjesSubstitution FrozenLinearCurveProfile ContinuousFirstLevelCrossing
  RiemannianTensorUP RiemannianCurveCost RiemannianCurveRetraction
  RiemannianCurveSubinterval RiemannianCurvePrefixBound
  RiemannianDistanceUP RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_distance_departure_lower]: every
    actual curve reaching outside the comparison ball first
    reaches its boundary, where the local distance estimate
    applies. This is the positive departure bound underlying
    the metric assertion in Federer 3.2.46, p. 281. *)
Lemma riemannian_distance_departure_lower (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (L : {linear R_n R n -> R_n R n}) o y (r k : R) :
  0 < r ->
  (forall z, inner_norm (@euclidean_inner_productP R n) (L (z-o)) <= r ->
    (((k*inner_norm (@euclidean_inner_productP R n) (L (z-o)))%R)%:E <=
      @riemannian_distance R n A g o z)%E) ->
  r < inner_norm (@euclidean_inner_productP R n) (L (y-o)) ->
  ((k*r)%:E <= @riemannian_distance R n A g o y)%E.
Proof.
move=> hr hLocal hFar.
apply: (riemannian_distance_greatest (riemannian_distance_laws A g o y)).
move=> C a b hC.
pose D := fun t : real_line_metric R=>C (segment_retraction a b t).
have hD : is_riemannian_admissible_curve A o y D a b := riemannian_retracted_curve_admissible hC.
have [ell [hEll hBound]] := hC.2.1.
have hGlobal := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b ell hC.1 hBound.
pose f := fun t : real_line_metric R=>inner_norm (@euclidean_inner_productP R n) (L (D t-o)).
have hf : continuous (f : real_line_metric R -> real_line_metric R).
  exact (@frozen_linear_curve_profile_continuous R n L o D ell hGlobal).
have hDa : D a = o := hD.2.2.2.1.
have hDb : D b = y := hD.2.2.2.2.
have hStart : f a < r by rewrite /f hDa subrr linear0 inner_norm0.
have hEnd : r < f b by rewrite /f hDb.
have [u [hu [hHit hPrefix]]] := @continuous_first_level_crossing R f a b r
  hC.1 (continuous_subspaceT hf) hStart hEnd.
have /andP [hau hub] := hu.
have hTime : a <= u <= b by rewrite (ltW hau) (ltW hub).
have hPrefixAd := riemannian_admissible_curve_subinterval hD (lexx a) (ltW hau) (ltW hub).
change (is_riemannian_admissible_curve A (D a) (D u) D a u) in hPrefixAd.
rewrite hDa in hPrefixAd.
have hLevel : inner_norm (@euclidean_inner_productP R n) (L (D u-o)) = r := hHit.
have hNear : inner_norm (@euclidean_inner_productP R n) (L (D u-o)) <= r.
  by rewrite hLevel.
have hLower := hLocal (D u) hNear; rewrite hLevel in hLower.
have hInf := riemannian_distance_curve_bound (riemannian_distance_laws A g o (D u)) hPrefixAd.
have hPrefixBound := riemannian_curve_prefix_cost_bound hg hD hTime.
have hLong := le_trans hLower (le_trans hInf hPrefixBound).
have hCost : riemannian_curve_cost g D a b = riemannian_curve_cost g C a b.
  exact: esym (riemannian_retracted_curve_cost hg hC).
by rewrite hCost in hLong.
Qed.
