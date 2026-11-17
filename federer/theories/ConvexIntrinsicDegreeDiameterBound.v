(** Supporting Federer (1969), 3.2.45, p. 280:
    average the original projected-body estimate in its two actual
    projection orders. The existing projection composition theorem
    identifies the lower-degree mean with its original normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionComposition
  EuclideanProjectionConvexImage EuclideanProjectionBoundedImage OrthogonalProjectionProbability
  HausdorffDiameterCost ProjectedVolumeMeasurability ConvexIntrinsicVolumeIntegrals
  ConvexProjectedIntrinsicVolumeAverage IntegralGeometricGauge ProjectionBeta
  TotalNonnegativeExtendedScaleIntegral PartialFunctionBasic PartialExtendedOrderLoci ExtendedRealOrderTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralComparison
  ConvexProjectionDegreeBound ProjectionDiameterCostContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_intrinsic_degree_diameter_bound]: the degree
    comparison used before the cube-product estimate in Federer
    3.2.45, p. 280, with the actual Hausdorff diameter coefficient
    retained. All original bounded convex sets and natural degree
    differences, including zero, are included. *)
Theorem convex_intrinsic_degree_diameter_bound (R:realType) n r k
    (hJN:((r+k)<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  (@projection_beta R n (r+k) hJN 1)%:E*@integral_geometric_gauge R n (r+k) hJN 1 S<=
    hausdorff_diameter_cost r S*
      ((@projection_beta R n k (leq_trans (leq_addl r k) hJN) 1)%:E*
        @integral_geometric_gauge R n k (leq_trans (leq_addl r k) hJN) 1 S).
Proof.
move=>hNonempty hConvex hBound.
pose P:=orthogonal_projection_metric_space R n (r+k).
pose mu:=@orthogonal_projection_probability R n (r+k) hJN.
have hMu:=@theta_star_is_measure R n (r+k) hJN.
have [C hC]:=@euclidean_projection_composition_exists R n (r+k) k.
pose f(p:P):extended_real_line R:=(@projection_beta R (r+k) k (leq_addl r k) 1)%:E*
  @integral_geometric_gauge R (r+k) k (leq_addl r k) 1 (euclidean_projection_linear p @` S).
have hIntegral:=@convex_intrinsic_volume_integral R n (r+k) hJN S hNonempty hConvex hBound.
have hAverage:=@convex_projected_intrinsic_volume_average R n (r+k) k hJN (leq_addl r k)
  C S hC hNonempty hConvex hBound.
have hFPositive p:0<=f p.
  have hImage:euclidean_projection_linear p @` S!=set0.
    have [a ha]:=hNonempty;exists (euclidean_projection_linear p a);by exists a.
  apply:mule_ge0;first by rewrite lee_fin;exact:ltW (@projection_beta_positive R (r+k) k (leq_addl r k) 1 (lexx 1)).
  exact:(@convex_intrinsic_volume_nonnegative_finite R (r+k) k (leq_addl r k) 1
    (euclidean_projection_linear p @` S) hImage
    (@euclidean_projection_convex_image R n (r+k) p S hConvex)
    (@euclidean_projection_bounded_image R n (r+k) p S hBound) (lexx 1)).1.
have hScaled:=@total_nonnegative_extended_scale_integral R P mu hMu f _ (hausdorff_diameter_cost r S)
  hFPositive hAverage (hausdorff_diameter_cost_nonnegative r S).
apply:(@measure_integral_monotone R P mu hMu _ _ _ _ hIntegral hScaled).
apply:(@measure_almost_everywhere_mono R P mu hMu setT _ _ (measure_almost_everywhere_true hMu))=>p _.
exists (projected_volume_function S p),(hausdorff_diameter_cost r S*f p);split=>//;split=>//.
have hImage:euclidean_projection_linear p @` S!=set0.
  have [a ha]:=hNonempty;exists (euclidean_projection_linear p a);by exists a.
have hLocal:=@convex_projection_degree_bound R r k (euclidean_projection_linear p @` S)
  hImage (@euclidean_projection_convex_image R n (r+k) p S hConvex)
    (@euclidean_projection_bounded_image R n (r+k) p S hBound).
apply:(le_trans hLocal).
have hCost:=@euclidean_projection_diameter_cost_contraction R n (r+k) r p S.
have hFinal:=lee_wpmul2r (hFPositive p) hCost.
exact hFinal.
Qed.
