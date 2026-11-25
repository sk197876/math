(** Concrete regressions for the completed continuity assertion
    of Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanCoordinateMetric
  IntegralGeometricGauge IntegralGeometricMeasure ProjectionBeta ConvexIntegralGeometricContinuity
  ProjectedVolumeMeasurability EuclideanProjectionMetric ZeroDegreeIntegralGauge
  OrthogonalProjectionProbability NonnegativeExtendedProbabilityConstant
  ExtendedRealOrderTopology ExtendedRealOrderLimit ConvexExponentSecantCounterexample.
From FedererTests Require Import ConvexExponentExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [unit_segment_continuity_with_source_estimate_failure]:
    concrete regression for Federer 3.2.45, p. 279. The
    actual unit segment has constant Q_t mass one, and
    its full extended-exponent family is continuous, while
    the original quantitative bound still fails. This
    checks that the correction does not discard continuity
    or the already proved actual-set counterexample. *)
Example unit_segment_continuity_with_source_estimate_failure (R : realType) (hMN : (1 <= 3)%N) :
  continuous (fun t : subspace [set t : extended_real_line R | (1 <= t)%E] =>
    (@convex_integral_geometric_measure R 3 1 hMN t
      (@euclidean_coordinate_line R 3 ord0 0 @` `[(0%R:R),1%R]) : extended_real_line R)) /\
  (forall t : \bar R, (1 <= t)%E -> @convex_integral_geometric_measure R 3 1 hMN t
    (@euclidean_coordinate_line R 3 ord0 0 @` `[(0%R:R),1%R]) = 1%E) /\
  Num.sqrt (2 : R) < (@projection_beta R 3 1 hMN (2 : R)%:E)^-1.
Proof.
split; first exact: convex_integral_geometric_measure_continuous.
exact: unit_segment_zero_reciprocal_regression.
Qed.

(** Source for [zero_degree_profile_every_exponent]: concrete
    boundary regression for the degree-zero extension used
    in the proof of Federer 3.2.45, p. 279. Every
    nonempty original source has projection profile constantly
    one in dimension zero, so every beta-normalized gauge
    is exactly one, including the infinity exponent.
    No compactness, convexity or measurability premise is needed. *)
Example zero_degree_profile_every_exponent (R : realType) n (h0N : (0 <= n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (t : \bar R) :
  S !=set0 -> (1 <= t)%E ->
  ((@projection_beta R n 0 h0N t)%:E * @integral_geometric_gauge R n 0 h0N t S = 1)%E.
Proof.
move=> hNonempty hT.
rewrite (@integral_geometric_gauge_normalized R n 0 h0N t hT S).
have hFunction : projected_volume_function (m:=0) S =
    (fun _ : orthogonal_projection_metric_space R n 0 => (1%E : extended_real_line R)).
  apply: funext=> p; exact: zero_degree_projected_volume hNonempty.
rewrite hFunction.
exact: (@probability_extended_norm_one R _ _ (@theta_star_is_measure R n 0 h0N) t
  (@theta_star_total R n 0 h0N) hT).
Qed.
