(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: one finite-exponent lower factor works for every
    compact convex source in the fixed original dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeGauge ProjectedVolumeMeasurability
  CompactConvexProjectedGaugeFinite NormalizedConvexProjectionProfileUP NormalizedConvexProjectionProfileExists
  CompactFullSupportProbabilityBalls ProbabilityLipschitzProfileLower OrthogonalProjectionProbability
  ProjectionProbabilitySupport ProjectionBeta IntegralGeometricGauge RealPower
  MeasureUP MeasurableFunctionUP PartialFunctionBasic MeasurableTotalBasic BorelFunctionBasic
  ScalarNormExtendedEmbedding ExtendedRealOrderTopology NonnegativeExtendedExponentNorm
  NonnegativeExtendedScalarNorm NonnegativeExtendedNormScale MeasureExponentDomain MeasureLpNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_compact_convex_projection_norm_lower]:
    expanded support for the corrected exponent infinity argument
    in Federer 3.2.45, p. 279. For each 0<r<1 one positive
    finite a, depending only on r and the dimensions, gives
    r a^(1/p) C_infinity(K) <= beta_p zeta_p(K) for every
    compact convex K and finite p>=1. Zero source supremum,
    empty bodies and degree zero are included. *)
Theorem uniform_compact_convex_projection_norm_lower (R : realType) n m (hMN : (m <= n)%N)
    (r : R) :
  (0 < r)%R -> (r < 1)%R -> exists a : R, (0 < a)%R /\
  forall (K : set (inner_metric_space (@euclidean_inner_productP R n))) (p : R),
    compact K -> is_inner_convex K -> (1 <= p)%R ->
    ((r * real_power a (p^-1))%R)%:E * @projected_volume_gauge R n m K <=
      (@projection_beta R n m hMN p%:E)%:E * @integral_geometric_gauge R n m hMN p%:E K.
Proof.
move=> hR hR1.
pose P := orthogonal_projection_metric_space R n m.
pose mu := @orthogonal_projection_probability R n m hMN.
have hMu : is_measure mu := @theta_star_is_measure R n m hMN.
pose L : R := m%:R.
pose delta : R := ((1-r)/(L+1))%R.
have hL : (0 <= L)%R := ler0n R m.
have hDenominator : (0 < L+1)%R by lra.
have hDenominatorNe : (L+1)%R != 0%R := lt0r_neq0 hDenominator.
have hDelta : (0 < delta)%R by rewrite /delta divr_gt0 // subr_gt0.
have hIdentity : ((L+1)*delta = 1-r)%R.
  by rewrite /delta mulrC divfK.
have hGap : (L*delta < 1-r)%R by move: hIdentity; rewrite mulrDl mul1r; lra.
have hSupport (U : set P) : open U -> U !=set0 -> 0 < mu U.
  exact: (@theta_star_nonempty_open_positive R n m hMN U).
have [a [hA hFloor]] := @compact_full_support_probability_ball_floor R P mu hMu
  (@euclidean_projection_space_compact R n m) (@theta_star_total R n m hMN) hSupport delta hDelta.
exists a; split=> // K p hCompact hConvex hP.
have hPE : 1 <= p%:E by rewrite lee_fin.
rewrite (@integral_geometric_gauge_normalized R n m hMN p%:E hPE K).
pose c : R := fine (@projected_volume_gauge R n m K).
have hCValue : @projected_volume_gauge R n m K = c%:E :=
  @compact_convex_projected_gauge_finite_value R n m hMN K hCompact hConvex.
have hc : (0 <= c)%R.
  have h := @projected_volume_gauge_nonnegative R n m K hMN.
  by rewrite hCValue lee_fin in h.
case: (eqVneq c 0%R)=> [hZero|hNonzero].
- rewrite hCValue hZero mule0.
  have hSuslin : SuslinSetUP.is_suslin_set R K.
    apply: BorelClosedProjection.metric_borel_suslin; apply: TopologicalBorel.closed_borel_set.
    exact: compact_closed (@metric_hausdorff R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) hCompact.
  exact: (@nonnegative_extended_exponent_norm_ge0 R P mu (projected_volume_function K) p%:E
    hMu (fun q => projected_volume_function_nonnegative K q) hPE
    (@theta_star_projected_volume_measurable R n m hMN K hSuslin)).
- have hcPositive : (0 < c)%R by rewrite lt_neqAle eq_sym hNonzero hc.
  have [f hF] := @normalized_convex_projection_profile_exists R n m hMN K c
    hCompact hConvex hcPositive hCValue.
  have hLower := @probability_lipschitz_profile_norm_lower R P mu hMu f L delta r a p
    (@theta_star_total R n m hMN) hL hDelta hR hA hGap hP
    (normalized_projection_profile_nonnegative hF) (normalized_projection_profile_attained_one hF)
    (normalized_projection_profile_relative_modulus hF) hFloor (normalized_projection_profile_measurable hF).
  have hEmbedding : nonnegative_extended_exponent_norm mu (fun q => (f q)%:E) p%:E =
      measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f).
    exact: (@nonnegative_extended_norm_scalar_embedding R P mu hMu f p%:E
      (normalized_projection_profile_nonnegative hF) hPE (normalized_projection_profile_measurable hF)).
  rewrite -hEmbedding in hLower.
  have hMeasurable : is_measure_measurable_function mu
      (partial_function_total (fun q => ((f q)%:E : extended_real_line R))).
    apply: (@measurable_total_borel_postcomposition R P
      [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
      (extended_real_line R) mu hMu f (fun y => (y%:E : extended_real_line R))
      (normalized_projection_profile_measurable hF)).
    apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
  have hScale := @nonnegative_extended_norm_scale R P mu hMu (fun q => (f q)%:E) p%:E c
    (fun q => lee_tofin (normalized_projection_profile_nonnegative hF q)) hPE hc hMeasurable.
  have hFunctions : projected_volume_function (m:=m) K =
      (fun q : P => (c%:E * (f q)%:E : extended_real_line R)).
    apply: funext=> q.
    by rewrite (normalized_projection_profile_value hF q) EFinM.
  rewrite hCValue hFunctions hScale [X in X <= _]muleC.
  have hScaled := lee_wpmul2l (lee_tofin hc) hLower.
  exact hScaled.
Qed.
