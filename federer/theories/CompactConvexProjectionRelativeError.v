(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: projected-volume profiles have a relative modulus
    uniform over every original compact convex source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionRows EuclideanRowFamily
  ConvexLinearImageRowsPerturbation CompactConvexProjectedGaugeFinite ProjectedVolumeGauge
  ProjectedVolumeMeasurability EuclideanLebesgueDimensions MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_projection_relative_error]: an
    expanded supporting theorem for the continuity assertion of
    Federer 3.2.45, p. 279. The sum of the actual row errors
    gives |Vol(p(K))-Vol(q(K))| <= m dist(p,q) C_infinity(K).
    This uses the original restricted Hom metric and original
    projected-volume supremum. All natural degree endpoints,
    empty sources and zero projection volumes are retained. *)
Theorem compact_convex_projection_relative_error (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> is_inner_convex K ->
  forall p q : orthogonal_projection_metric_space R n m,
  (`|fine (projected_volume_function K p)-fine (projected_volume_function K q)| <=
    m%:R * mdist p q * fine (@projected_volume_gauge R n m K))%R.
Proof.
move=> hCompact hConvex.
case: m hMN=> [hMN p q|m hMN p q].
- have hImages : euclidean_projection_linear p @` K = euclidean_projection_linear q @` K.
    apply: eq_imagel=> x _.
    by rewrite (coordinate_zero (euclidean_projection_linear p x))
      (coordinate_zero (euclidean_projection_linear q x)).
  by rewrite /projected_volume_function hImages subrr normr0 !mul0r.
- pose C := @projected_volume_gauge R n m.+1 K.
  have hCValue := @compact_convex_projected_gauge_finite_value R n m.+1 hMN K hCompact hConvex.
  have hCFinite := @compact_convex_projected_gauge_finite R n m.+1 hMN K hCompact hConvex.
  have hNorm (r : orthogonal_projection_metric_space R n m.+1) i :
      (inner_norm (@euclidean_inner_productP R n) (euclidean_projection_rows r i) <= 1)%R.
    by rewrite euclidean_projection_row_norm.
  have hDifference i :
      (inner_norm (@euclidean_inner_productP R n)
        (euclidean_projection_rows p i-euclidean_projection_rows q i) <= mdist p q)%R.
    exact: euclidean_projection_row_difference_bound.
  have hReverseDifference i :
      (inner_norm (@euclidean_inner_productP R n)
        (euclidean_projection_rows q i-euclidean_projection_rows p i) <= mdist p q)%R.
    have h := euclidean_projection_row_difference_bound q p i.
    by rewrite metric_sym in h.
  have hForward := @convex_linear_image_rows_perturbation R n m K
    (euclidean_projection_rows p) (euclidean_projection_rows q)
    (euclidean_projection_linear p) (euclidean_projection_linear q) (mdist p q)
    hMN hCompact hConvex (euclidean_projection_rows_laws p) (euclidean_projection_rows_laws q)
    (hNorm p) (hNorm q) hDifference.
  have hReverse := @convex_linear_image_rows_perturbation R n m K
    (euclidean_projection_rows q) (euclidean_projection_rows p)
    (euclidean_projection_linear q) (euclidean_projection_linear p) (mdist p q)
    hMN hCompact hConvex (euclidean_projection_rows_laws q) (euclidean_projection_rows_laws p)
    (hNorm q) (hNorm p) hReverseDifference.
  have hValue (r : orthogonal_projection_metric_space R n m.+1) :
      @euclidean_lebesgue_measure R m.+1 (euclidean_projection_linear r @` K) =
        (fine (projected_volume_function K r))%:E.
    symmetry; apply: fineK.
    rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R m.+1) _)).
    apply: le_lt_trans _ hCFinite.
    exact: (@projected_volume_gauge_projection_bound R n m.+1 K
      (euclidean_projection_linear r) (euclidean_projection_linear_member r)).
  rewrite !hValue hCValue -EFinM -EFinD lee_fin in hForward hReverse.
  change (is_true ((fine (projected_volume_function K p) <= fine (projected_volume_function K q) +
    m.+1%:R * mdist p q * fine (@projected_volume_gauge R n m.+1 K))%R)) in hForward.
  change (is_true ((fine (projected_volume_function K q) <= fine (projected_volume_function K p) +
    m.+1%:R * mdist p q * fine (@projected_volume_gauge R n m.+1 K))%R)) in hReverse.
  rewrite ler_norml; apply/andP; split; lra.
Qed.
