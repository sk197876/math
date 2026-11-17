(** Existence for the independent normalized-profile laws supporting
    Federer (1969), 3.2.45, p. 279. The normalization is used
    only when the actual source projection supremum is positive. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeGauge ProjectedVolumeMeasurability
  CompactConvexProjectionRelativeError CompactConvexProjectionMaximum
  NormalizedConvexProjectionProfileUP EuclideanLebesgueDimensions MeasureUP
  TopologicalBorel BorelClosedProjection SuslinSetUP BoundedProjectedVolumeNorm
  PartialFunctionBasic MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic NormMetricScaleContinuity
  OrthogonalProjectionProbability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [normalized_convex_projection_profile_exists]:
    expanded support for the corrected continuity proof of Federer
    3.2.45, p. 279. The original finite positive projection
    supremum justifies normalization. The proved relative modulus,
    attained maximum, and original projected-volume measurability
    supply every independent profile law. Division serves only to
    prove existence; no globally selected profile is introduced. *)
Theorem normalized_convex_projection_profile_exists (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  compact K -> is_inner_convex K -> (0 < c)%R ->
  @projected_volume_gauge R n m K = c%:E ->
  exists f : orthogonal_projection_metric_space R n m ->
      real_norm_metric_space (scalar_absolute_value_norm R),
    is_normalized_convex_projection_profile hMN K c f.
Proof.
move=> hCompact hConvex hc hCValue.
pose P := orthogonal_projection_metric_space R n m.
pose f (p : P) : real_norm_metric_space (scalar_absolute_value_norm R) :=
  (fine (projected_volume_function K p) / c)%R.
have hc0 : c != 0%R := lt0r_neq0 hc.
have hBound (p : P) : projected_volume_function K p <= c%:E.
  rewrite -hCValue.
  exact: (@projected_volume_gauge_projection_bound R n m K (euclidean_projection_linear p)
    (euclidean_projection_linear_member p)).
have hFinite (p : P) : projected_volume_function K p \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R m) _)).
  exact: le_lt_trans (hBound p) (ltry c).
have hScalar (p : P) : (c*f p = fine (projected_volume_function K p))%R.
  by rewrite /f mulrC divfK.
have hNonnegative (p : P) : (0 <= fine (projected_volume_function K p))%R.
  have h := projected_volume_function_nonnegative K p.
  by rewrite -(fineK (hFinite p)) lee_fin in h.
exists f; constructor.
- move=> p; rewrite hScalar; symmetry; exact: fineK (hFinite p).
- move=> p; exact: divr_ge0 (hNonnegative p) (ltW hc).
- move=> p; rewrite /f ler_pdivrMr // mul1r.
  have h := hBound p; by rewrite -(fineK (hFinite p)) lee_fin in h.
- have [p hP] := @compact_convex_projection_maximum R n m hMN K hCompact hConvex.
  exists p; by rewrite /f hP hCValue /= divff.
- move=> p q.
  have h := @compact_convex_projection_relative_error R n m hMN K hCompact hConvex p q.
  rewrite hCValue /= -(hScalar p) -(hScalar q) -mulrBr normrM (ger0_norm (ltW hc)) in h.
  have hOrder : (m%:R*mdist p q*c = c*(m%:R*mdist p q))%R by ring.
  by rewrite hOrder (ler_pM2l hc) in h.
- have hSuslin : is_suslin_set R K.
    apply: metric_borel_suslin; apply: closed_borel_set.
    exact: compact_closed (@metric_hausdorff R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) hCompact.
  have hMeasurable := @projected_volume_scalar_measurable R n m hMN K hSuslin.
  have hScale : continuous (fun y : real_norm_metric_space (scalar_absolute_value_norm R) =>
      ((y/c)%R : real_norm_metric_space (scalar_absolute_value_norm R))).
    have hFunction : (fun y : real_norm_metric_space (scalar_absolute_value_norm R) =>
        ((y/c)%R : real_norm_metric_space (scalar_absolute_value_norm R))) =
      (fun y => ((c^-1)%R *: y : real_norm_metric_space (scalar_absolute_value_norm R))).
      apply: funext=> y; exact: mulrC.
    rewrite hFunction.
    exact: real_norm_metric_scale_continuous.
  exact: (@measurable_total_borel_postcomposition R P
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (@orthogonal_projection_probability R n m hMN) (@theta_star_is_measure R n m hMN)
    (projected_volume_scalar (m:=m) K) (fun y => ((y/c)%R : real_norm_metric_space (scalar_absolute_value_norm R)))
    hMeasurable (continuous_borel_function hScale)).
Qed.
