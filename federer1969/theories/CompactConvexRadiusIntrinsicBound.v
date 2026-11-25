(** Federer (1969), 3.2.38, p. 275: uniform lower-degree
    intrinsic coefficients from an actual containing ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex MetricClosedBalls
  EuclideanLebesgueDimensions EuclideanClosedBallVolume EuclideanBallVolume
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability
  ConvexIntrinsicVolumeIntegrals CompactSetDistanceProfile CompactMetricBounded
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralComparison
  ProbabilityConstantIntegral PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_radius_intrinsic_bound]: supporting the
    j<m error terms in Federer 3.2.38, p. 275. A ball about an
    actual point supplies a uniform projected-ball volume; integrate
    it against the actual orthogonal projection probability and
    divide by the proved positive beta. This weaker radius constant
    suffices for the printed xi/v error. The j=0 coefficient and
    radius zero are explicitly retained. *)
Lemma compact_convex_radius_intrinsic_bound (R:realType) n j (hjn:(j<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (c:inner_metric_space (@euclidean_inner_productP R n)) (d:R):
  compact S ->S!=set0 ->is_inner_convex S ->0<=d ->
  (forall x,S x ->mdist c x<=d) ->
  (@integral_geometric_gauge R n j hjn 1 S<=
    ((@projection_beta R n j hjn 1)^-1*(euclidean_unit_ball_volume R j*d^+j))%:E)%E.
Proof.
move=>hCompact hNonempty hConvex hd hRadius.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R j).
pose P:=orthogonal_projection_metric_space R n j.
pose theta:=@orthogonal_projection_probability R n j hjn.
pose B:R:=euclidean_unit_ball_volume R j*d^+j.
pose beta:R:=@projection_beta R n j hjn 1.
pose C:compact_metric_set X:=exist _ S (mem_set (conj hCompact hNonempty)).
have hProjected (p:P):(projected_volume_function S p<=B%:E)%E.
  rewrite /projected_volume_function /B -(@euclidean_closed_ball_normalized_volume R j
    (euclidean_projection_linear p c) d hd).
  apply:(@measure_mono R Y _ (euclidean_lebesgue_is_measure R j))=>y [x hx <-].
  exact:le_trans (euclidean_projection_nonexpanding p c x) (hRadius x hx).
have hIntegral:=@convex_intrinsic_volume_integral R n j hjn S
  hNonempty hConvex (compact_metric_diameter_finite C).
have hConstant:=@probability_constant_integral R P theta (@theta_star_is_measure R n j hjn)
  B (@theta_star_total R n j hjn).
have hAverage:(beta%:E*@integral_geometric_gauge R n j hjn 1 S<=B%:E)%E.
  apply:(@measure_integral_monotone R P theta (@theta_star_is_measure R n j hjn)
    _ _ _ _ hIntegral hConstant).
  apply:(@measure_almost_everywhere_mono R P theta (@theta_star_is_measure R n j hjn)
    setT _ _ (@measure_almost_everywhere_true R P theta (@theta_star_is_measure R n j hjn)))=>p _.
  exists (projected_volume_function S p),B%:E; split; first reflexivity.
  split; first reflexivity; exact:hProjected p.
have hBeta:0<beta:=@projection_beta_positive R n j hjn 1 (lexx 1%E).
have hBeta0:beta!=0 by rewrite gt_eqF.
have hInverse:(0<=(beta^-1)%:E)%E by rewrite lee_fin invr_ge0; exact:ltW hBeta.
have hBound:=lee_wpmul2l hInverse hAverage.
by rewrite muleA -EFinM mulVf // mul1e -EFinM in hBound.
Qed.
