(** Norm connections for the independently specified normalized
    projection profiles, supporting Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionMetric ProjectedVolumeGauge ProjectedVolumeMeasurability
  NormalizedConvexProjectionProfileUP UniformConvexProjectionNormLower
  OrthogonalProjectionProbability ProjectionBeta IntegralGeometricGauge RealPower
  MeasureUP MeasurableFunctionUP PartialFunctionBasic MeasurableTotalBasic BorelFunctionBasic
  ScalarNormExtendedEmbedding ExtendedRealOrderTopology NonnegativeExtendedExponentNorm
  NonnegativeExtendedScalarNorm NonnegativeExtendedNormScale MeasureExponentDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [normalized_projection_profile_norm_value]:
    expanded normalization connection for Federer 3.2.45,
    p. 279. The original beta-normalized gauge is the
    original positive finite supremum times the norm of
    the independently specified normalized profile, at
    every exponent, including infinity. *)
Theorem normalized_projection_profile_norm_value (R : realType) n m
    (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (f : orthogonal_projection_metric_space R n m ->
      real_norm_metric_space (scalar_absolute_value_norm R)) (t : \bar R) :
  (0 <= c)%R -> is_normalized_convex_projection_profile hMN K c f -> 1 <= t ->
  (@projection_beta R n m hMN t)%:E * @integral_geometric_gauge R n m hMN t K =
    c%:E * measure_exponent_norm (@orthogonal_projection_probability R n m hMN)
      (partial_function_total f) t.
Proof.
move=> hC hF hT.
pose P := orthogonal_projection_metric_space R n m.
pose mu := @orthogonal_projection_probability R n m hMN.
have hMu : is_measure mu := @theta_star_is_measure R n m hMN.
have hMeasurable : is_measure_measurable_function mu
    (partial_function_total (fun q => ((f q)%:E : extended_real_line R))).
  apply: (@measurable_total_borel_postcomposition R P
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hMu f (fun y => (y%:E : extended_real_line R))
    (normalized_projection_profile_measurable hF)).
  apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
have hFunctions : projected_volume_function (m:=m) K =
    (fun q : P => (c%:E * (f q)%:E : extended_real_line R)).
  apply: funext=> q; by rewrite (normalized_projection_profile_value hF q) EFinM.
rewrite (@integral_geometric_gauge_normalized R n m hMN t hT K) hFunctions.
rewrite (@nonnegative_extended_norm_scale R P mu hMu (fun q => (f q)%:E) t c
  (fun q => lee_tofin (normalized_projection_profile_nonnegative hF q)) hT hC hMeasurable).
by rewrite (@nonnegative_extended_norm_scalar_embedding R P mu hMu f t
  (normalized_projection_profile_nonnegative hF) hT (normalized_projection_profile_measurable hF)).
Qed.

(** Source for [normalized_projection_profile_uniform_norm_floor]:
    expanded uniform range bound for the corrected finite-exponent
    argument in Federer 3.2.45, p. 279. One d>0 works
    for all compact convex sources with positive original
    projection supremum and every normalized profile. The
    profile laws and value of the supremum are supplied by
    their proved existence theorem in applications. *)
Theorem normalized_projection_profile_uniform_norm_floor (R : realType) n m
    (hMN : (m <= n)%N) : exists d : R, (0 < d)%R /\
  forall (K : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (f : orthogonal_projection_metric_space R n m ->
      real_norm_metric_space (scalar_absolute_value_norm R)),
    compact K -> is_inner_convex K -> (0 < c)%R ->
    @projected_volume_gauge R n m K = c%:E ->
    is_normalized_convex_projection_profile hMN K c f ->
    d%:E <= measure_exponent_norm (@orthogonal_projection_probability R n m hMN)
      (partial_function_total f) 1.
Proof.
have hHalf : (0 < (1/2 : R))%R by lra.
have hHalfOne : ((1/2 : R) < 1)%R by lra.
have [a [hA hBound]] := @uniform_compact_convex_projection_norm_lower R n m hMN
  (1/2)%R hHalf hHalfOne.
exists (1/2*a)%R; split; first exact: mulr_gt0 hHalf hA.
move=> K c f hCompact hConvex hC hValue hF.
have h := hBound K 1%R hCompact hConvex (lexx 1%R).
rewrite invr1 real_power_one_exponent ?(ltW hA) // hValue
  (@normalized_projection_profile_norm_value R n m hMN K c f 1 (ltW hC) hF (lexx 1)) in h.
have hProduct : (((1/2*a)%R)%:E*c%:E = c%:E*((1/2*a)%R)%:E).
  exact: muleC.
rewrite hProduct in h.
by move: h; rewrite lee_pmul2l // lte_fin.
Qed.
