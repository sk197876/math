(** Corrected uniform finite-exponent comparison for the
    actual gauges in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionMetric ProjectedVolumeGauge CompactConvexProjectedGaugeFinite
  NormalizedConvexProjectionProfileUP NormalizedConvexProjectionProfileExists
  NormalizedConvexProjectionProfileNorm ProbabilityUnitProfileReciprocalSecant
  CompactConvexNormalizedGaugeZero IntegralGeometricGauge ProjectionBeta
  OrthogonalProjectionProbability MeasureExponentDomain MeasureReciprocalInterval ReciprocalExponent
  RealExponentialSealed RealExponentialLaws PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_uniform_reciprocal_secant]:
    corrected finite-exponent estimate supporting Federer
    3.2.45, p. 279. One nonnegative constant C, depending
    only on the dimensions, bounds the original normalized
    gauges by exp(C(v-u)/v), for 0<=u<v<=1.
    Compact convex sources may be empty or have zero
    projection supremum. The infinity reciprocal endpoint
    u=0 is included in the inequality, but continuity
    there uses the separate uniform projection modulus. *)
Theorem compact_convex_uniform_reciprocal_secant (R : realType) n m
    (hMN : (m <= n)%N) : exists C : R, (0 <= C)%R /\
  forall (K : set (inner_metric_space (@euclidean_inner_productP R n))) (u v : R),
    compact K -> is_inner_convex K -> (0 <= u)%R -> (u < v)%R -> (v <= 1)%R ->
    (@projection_beta R n m hMN (reciprocal_lebesgue_exponent u))%:E *
      @integral_geometric_gauge R n m hMN (reciprocal_lebesgue_exponent u) K <=
    (@RealExponential.exponential R
      (C * (v-u)/v)%R)%:E *
      ((@projection_beta R n m hMN (reciprocal_lebesgue_exponent v))%:E *
        @integral_geometric_gauge R n m hMN (reciprocal_lebesgue_exponent v) K).
Proof.
have [d0 [hD0 hFloor0]] := @normalized_projection_profile_uniform_norm_floor R n m hMN.
pose d := Order.min d0 1%R.
have hD : (0 < d)%R by rewrite /d lt_min hD0 ltr01.
have hD1 : (d <= 1)%R by rewrite /d ge_min lexx orbT.
have hDD0 : (d <= d0)%R by rewrite /d ge_min lexx.
pose C := (- RealExponential.logarithm d)%R.
have hC0 : (0 <= C)%R.
  have hLog : (RealExponential.logarithm d <= RealExponential.logarithm (1 : R))%R.
    by rewrite real_logarithm_order.
  rewrite real_logarithm_one in hLog.
  by rewrite /C oppr_ge0.
exists C; split=> // K u v hCompact hConvex hU hUV hV1.
have hU1 : (u <= 1)%R := le_trans (ltW hUV) hV1.
have hV : (0 <= v)%R := le_trans hU (ltW hUV).
have hUE := @reciprocal_lebesgue_exponent_domain R u hU hU1.
have hVE := @reciprocal_lebesgue_exponent_domain R v hV hV1.
pose c := fine (@projected_volume_gauge R n m K).
have hValue : @projected_volume_gauge R n m K = c%:E :=
  @compact_convex_projected_gauge_finite_value R n m hMN K hCompact hConvex.
have hC : (0 <= c)%R.
  have h := @projected_volume_gauge_nonnegative R n m K hMN.
  by rewrite hValue lee_fin in h.
case: (eqVneq c 0%R)=> [hZero|hNonzero].
- have hGaugeZero : @projected_volume_gauge R n m K = 0 by rewrite hValue hZero.
  by rewrite (@compact_convex_normalized_gauge_zero R n m hMN K _ hCompact hConvex hGaugeZero hUE)
    (@compact_convex_normalized_gauge_zero R n m hMN K _ hCompact hConvex hGaugeZero hVE) mule0.
- have hPositive : (0 < c)%R by rewrite lt_neqAle eq_sym hNonzero hC.
  have [f hF] := @normalized_convex_projection_profile_exists R n m hMN K c
    hCompact hConvex hPositive hValue.
  have hFUnit q : (`|f q| <= 1)%R.
    rewrite (ger0_norm (normalized_projection_profile_nonnegative hF q)).
    exact: normalized_projection_profile_unit_bound hF q.
  have hNorm := @probability_unit_profile_reciprocal_secant R _
    (@orthogonal_projection_probability R n m hMN) (@theta_star_is_measure R n m hMN)
    f d u v (@theta_star_total R n m hMN) hD hFUnit
    (normalized_projection_profile_measurable hF)
    (le_trans (lee_tofin hDD0) (hFloor0 K c f hCompact hConvex hPositive hValue hF)) hU hUV hV1.
  rewrite !measure_reciprocal_exponent_normE in hNorm.
  rewrite (@normalized_projection_profile_norm_value R n m hMN K c f _ hC hF hUE)
    (@normalized_projection_profile_norm_value R n m hMN K c f _ hC hF hVE).
  have hScaled := lee_wpmul2l (lee_tofin hC) hNorm.
  rewrite [X in _ <= X]muleCA in hScaled.
  exact hScaled.
Qed.
