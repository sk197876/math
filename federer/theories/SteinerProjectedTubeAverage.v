(** Federer (1969), 3.2.35, p. 272:
    apply the lower-dimensional tube formula to
    every actual projection, and integrate its
    finite polynomial with the proved marginal laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionComposition EuclideanProjectionConvexImage
  EuclideanProjectionBoundedImage ProjectionDistanceTube MetricSetDistanceUP MetricSetDistanceSealed
  ConvexProjectedIntrinsicVolumeRatio ConvexIntrinsicVolumeIntegrals ProjectedVolumeMeasurability
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability SteinerTubePolynomial EuclideanBallVolume
  ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralUP TotalNonnegativeExtendedScaleIntegral
  TotalFiniteNonnegativeIntegral MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [steiner_projected_tube_average]: the
    finite sum and the repeated projection
    integrals in Federer 3.2.35, p. 272.
    This supporting induction step explicitly
    receives only the lower-dimensional Steiner
    theorem. Original projected sets are nonempty
    bounded convex, their actual distances have
    existing opaque laws, and projection commutes
    exactly with the original tube. Proved
    finite integral interchange and actual beta
    ratios integrate every original coefficient.
    No hypothesis is added to the final theorem. *)
Theorem steiner_projected_tube_average (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d (t:R):
  (forall (A:set (inner_metric_space (@euclidean_inner_productP R k))) e,
    A!=set0 ->is_inner_convex A ->metric_set_bounded A ->is_metric_set_distance A e ->
    is_steiner_tube_volume A e) ->
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->(0<t)%R ->
  is_measure_integral (@orthogonal_projection_probability R k.+1 k (leqnSn k))
    (partial_function_total (projected_volume_function (m:=k) [set x|(d x<t)%R]))
    (\sum_(i:'I_k.+1) (euclidean_unit_ball_volume R (k-i)*t^+(k-i))%R%:E*
      ((@projection_beta R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 /
        @projection_beta R k i (steiner_dimension_guard i) 1)%R%:E*
      @integral_geometric_gauge R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S)).
Proof.
move=>hIH hNonempty hS hBound hD ht.
pose P:=orthogonal_projection_metric_space R k.+1 k.
pose theta:=@orthogonal_projection_probability R k.+1 k (leqnSn k).
pose T (p:P):set (inner_metric_space (@euclidean_inner_productP R k)):=euclidean_projection_linear p @` S.
have hTNonempty p:T p!=set0.
  have [a ha]:=hNonempty; exists (euclidean_projection_linear p a); by exists a.
have hTConvex p:is_inner_convex (T p):=@euclidean_projection_convex_image R k.+1 k p S hS.
have hTBound p:metric_set_bounded (T p):=@euclidean_projection_bounded_image R k.+1 k p S hBound.
pose c (i:'I_k.+1):=(euclidean_unit_ball_volume R (k-i)*t^+(k-i))%R.
pose g (i:'I_k.+1) (p:P):extended_real_line R:=
  @integral_geometric_gauge R k i (steiner_dimension_guard i) 1 (T p).
pose a (i:'I_k.+1):=(@projection_beta R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 /
  @projection_beta R k i (steiner_dimension_guard i) 1)%R%:E*
  @integral_geometric_gauge R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S.
have hCPositive i:(0<=c i)%R.
  apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R (k-i)).2.
  exact:exprn_ge0 _ (ltW ht).
have hGPositive i p:0<=g i p.
  exact:(@convex_intrinsic_volume_nonnegative_finite R k i (steiner_dimension_guard i) 1 (T p)
    (hTNonempty p) (hTConvex p) (hTBound p) (lexx 1)).1.
have hAIntegral i:is_measure_integral theta (partial_function_total (g i)) (a i).
  have [C hC]:=euclidean_projection_composition_exists R k.+1 k i.
  exact:(@convex_projected_intrinsic_volume_ratio R k.+1 k i (leqnSn k) (steiner_dimension_guard i)
    C S hC hNonempty hS hBound).
have hScaled i:is_measure_integral theta
    (partial_function_total (fun p:P=>((c i)%:E*g i p:extended_real_line R))) ((c i)%:E*a i).
  exact:(@total_nonnegative_extended_scale_integral R P theta
    (@theta_star_is_measure R k.+1 k (leqnSn k)) (g i) (a i) (c i)%:E
    (hGPositive i) (hAIntegral i) (lee_tofin (hCPositive i))).
have hPositive i p:0<=(c i)%:E*g i p:=mule_ge0 (lee_tofin (hCPositive i)) (hGPositive i p).
have hSum:=@total_finite_nonnegative_integral R P [the finType of 'I_k.+1] theta
  (@theta_star_is_measure R k.+1 k (leqnSn k))
  (fun i p=>((c i)%:E*g i p:extended_real_line R)) (fun i=>(c i)%:E*a i) hPositive hScaled.
have hFunction:projected_volume_function (m:=k) [set x|(d x<t)%R]=
    (fun p:P=>(\sum_i (c i)%:E*g i p:extended_real_line R)).
  apply:funext=>p.
  pose e:=@MetricSetDistance.value R [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]
    (T p) (hTNonempty p).
  have hE:is_metric_set_distance (T p) e:=MetricSetDistance.laws (hTNonempty p).
  have hImage:=@projection_distance_tube R k.+1 k p S d e t hD hE.
  have hLower:=hIH (T p) e (hTNonempty p) (hTConvex p) (hTBound p) hE t ht.
  rewrite /projected_volume_function hImage hLower /steiner_tube_polynomial.
  apply:eq_bigr=>i _; exact:muleC.
by rewrite hFunction.
Qed.
