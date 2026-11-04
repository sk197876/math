(** Federer (1969), 3.2.48, pp. 284, 286: original signed
    summable weights pull back to the actual source product.
    The actual all-set Cartesian measure equality and 2.6.4 justify
    absolute summability before any signed Fubini interchange. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts ProductInner UnitSphereSpace
  SphericalProductPreimageImage SphericalOrthogonalPullback SphericalMeasurablePullback
  SphericalWeightedPullback SphericalPullbackPushforward RectifiableSetUP RectifiableFiniteHausdorffMass
  HausdorffMeasure MeasureUP MeasureRestriction MeasureIntegralUP MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialFunctionPrecomposition SummableRealFunctionUP
  FiniteInnerCompletedCartesianMeasure ProductMeasure SeparatedProductIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_weighted_pullback_real_integral]: the actual
    finite signed factor integral used in the last display of 3.2.48,
    p. 286. This retains the original completed measurable source and
    derives pullback summability from the original summable weight. *)
Theorem spherical_weighted_pullback_real_integral (R:realType) d r (c:R_n R d.+1)
    (A:set (R_n R d.+1)) (alpha:R_n R d.+1->R) a:
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r) r A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r) A ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r) A)
    (real_total_integrand alpha) a%:E ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1)) (r+d*(d-1)%/2))
    (spherical_orthogonal_preimage c A))
    (real_total_integrand (fun g:Hom (R_n R d.+1) (R_n R d.+1)=>alpha (g c)))
    (spherical_preimage_mass_scale R d r*a)%:E.
Proof.
move=>hc hA hRA hMA hAlpha.
have hPull:=@spherical_weighted_pullback_integral R d r c A (real_total_integrand alpha)
  a%:E hc hA hRA hMA hAlpha.
rewrite -EFinM in hPull.
apply:(measure_integral_graph_equivalent _ hPull)=>g z.
change (partial_function_graph (real_total_integrand alpha) (g c) z <->
  partial_function_graph (real_total_integrand (fun g:Hom (R_n R d.+1) (R_n R d.+1)=>alpha (g c))) g z).
by rewrite !real_total_integrand_graph.
Qed.

(** Source for [spherical_kinematic_source_weight_integral]: actual
    signed separated source integral in 3.2.48, p. 286, before
    insertion of the Jacobian. Genuine rectifiability of B proves the
    required product measure equality; no product integrability is assumed. *)
Theorem spherical_kinematic_source_weight_integral (R:realType) d k m (c:R_n R d.+1)
    (A B:set (R_n R d.+1)) (alpha beta:R_n R d.+1->R) a b:
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->B `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R d.+1)) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) m) B ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) A) (real_total_integrand alpha) a%:E ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) m) B) (real_total_integrand beta) b%:E ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)) in
  is_measure_integral (measure_restrict (@hausdorff_measure R P
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    [set z:Hom (R_n R d.+1) (R_n R d.+1)*Hom (R_n R d.+1) (R_n R d.+1)|
      spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2])
    (real_total_integrand (fun z:Hom (R_n R d.+1) (R_n R d.+1)*Hom (R_n R d.+1) (R_n R d.+1)=>alpha (z.1 c)*beta (z.2 c)))
    ((spherical_preimage_mass_scale R d k*a)*(spherical_preimage_mass_scale R d m*b))%:E.
Proof.
move=>hc hA hB hRA hMA hRB hMB hAlpha hBeta P.
have hRBF:=rectifiable_hausdorff_measure_rectifiable hRB.
have hAlphaPull:=spherical_weighted_pullback_real_integral hc hA hRA hMA hAlpha.
have hBetaPull:=spherical_weighted_pullback_real_integral hc hB hRBF hMB hBeta.
have hX:=@spherical_measurable_measure_rectifiable_pullback R d k c A hc hA hRA hMA.
have hY:=@spherical_measurable_measure_rectifiable_pullback R d m c B hc hB hRBF hMB.
have hYGenuine:=@federer_3_2_47_1 R d c B m hc hB hRB.
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R d.+1 d.+1.
rewrite (@finite_inner_completed_cartesian_measure_right R
  (Hom (R_n R d.+1) (R_n R d.+1)) (Hom (R_n R d.+1) (R_n R d.+1)) _ _
  (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)
  _ _ e p e p (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N
  (spherical_orthogonal_preimage c A) (spherical_orthogonal_preimage c B)
  hChart hChart hX.1 hX.2 hYGenuine hY.2).
exact (separated_product_integral _ _ hAlphaPull hBetaPull).
Qed.
