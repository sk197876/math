(** Supporting Federer (1969), 3.2.45, p. 280:
    integrate the already proved Fubini–isodiametric projection
    estimate to bound volume by a lower intrinsic coefficient.
    All original bounded convex bodies and zero degrees remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionProbability
  OrthogonalProjectionVolumeBound EuclideanLebesgueDimensions HausdorffDiameterCost
  ProjectedVolumeMeasurability ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge ProjectionBeta
  PositiveCharacteristicMeasurability TotalNonnegativeExtendedScaleIntegral PartialFunctionBasic
  PartialExtendedOrderLoci ExtendedRealOrderTopology MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_projection_degree_bound]: supporting the
    degree-drop estimate used for the final product formula in
    Federer 3.2.45, p. 280. Average the existing actual outer-volume
    projection bound; the original normalization and diameter power
    are retained. No mixed-volume monotonicity premise is added. *)
Theorem convex_projection_degree_bound (R:realType) r k
    (S:set (inner_metric_space (@euclidean_inner_productP R (r+k)))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  euclidean_lebesgue_measure (r+k) S<=
    hausdorff_diameter_cost r S*
      ((@projection_beta R (r+k) k (leq_addl r k) 1)%:E*
        @integral_geometric_gauge R (r+k) k (leq_addl r k) 1 S).
Proof.
move=>hNonempty hConvex hBound.
pose P:=orthogonal_projection_metric_space R (r+k) k.
pose mu:=@orthogonal_projection_probability R (r+k) k (leq_addl r k).
have hMu:=@theta_star_is_measure R (r+k) k (leq_addl r k).
pose f:=projected_volume_function (m:=k) S.
pose c:=hausdorff_diameter_cost r S.
have hIntegral:=@convex_intrinsic_volume_integral R (r+k) k (leq_addl r k) S hNonempty hConvex hBound.
have hScaled:=@total_nonnegative_extended_scale_integral R P mu hMu f _ c
  (fun p=>projected_volume_function_nonnegative S p) hIntegral (hausdorff_diameter_cost_nonnegative r S).
have hConstant:=@PositiveCharacteristicMeasurability.nonnegative_extended_constant_integral R P mu hMu
  (euclidean_lebesgue_measure (r+k) S)
  (measure_nonnegative (euclidean_lebesgue_is_measure R (r+k)) S).
rewrite /mu theta_star_total mule1 in hConstant.
apply:(@measure_integral_monotone R P mu hMu _ _ _ _ hConstant hScaled).
apply:(@measure_almost_everywhere_mono R P mu hMu setT _ _ (measure_almost_everywhere_true hMu))=>p _.
exists (euclidean_lebesgue_measure (r+k) S),(c*f p);split=>//;split=>//.
rewrite /c /f /projected_volume_function muleC.
exact:(@orthogonal_projection_outer_volume_bound R r k (euclidean_projection_linear p) S
  (euclidean_projection_linear_member p)).
Qed.
