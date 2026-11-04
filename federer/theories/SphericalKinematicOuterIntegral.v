(** Federer (1969), 3.2.48, p. 284: the original
    intersection integral is obtained from the actual whole-fibre
    coarea integral and the positive Haar normalization. Signed
    definedness, exceptional fibres and infinite values are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanInnerProduct InnerNorm InnerMetric EuclideanHomInnerCharts ProductInner OrthogonalMaps
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology TopologicalGroupUP HomSpaceTopology
  HaarIntegralUP CompactGroupHaarNormalisation OrthogonalHausdorffHaarTransport OrthogonalHausdorffHaarAlmost
  OrthogonalKinematicMap OrthogonalKinematicCoareaFibres SphericalProductPreimageImage
  SphericalKinematicFibreIntegrals SphericalKinematicIntegral SphericalKinematicSourceAverage
  SphericalPullbackPushforward StiefelGammaVolumeScalar RectifiableSetUP UnitSphereSpace HausdorffMeasure
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence MeasureIntegralScaleLaw
  MeasureSubsetIntegral RestrictedIntegralIdentity ParameterizedIntegral PartialFunctionUP
  PartialFunctionPrecomposition PartialZeroExtension MeasurableExtendedScale MeasureUpperIntegralScale SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_outer_integral]: the change of
    outer integral in the last display of 3.2.48, p. 284. The
    whole-fibre regularity used by both signed fibre changes is proved
    by actual coarea from the printed A,B hypotheses. No independent
    original-intersection integrability or measurability premise occurs. *)
Theorem spherical_kinematic_outer_integral (R:realType) d k m (c:R_n R (1+d))
    (A B:set (R_n R (1+d))) (alpha beta:R_n R (1+d)->R)
    (mulS:euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d))
    (invS:euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d))
    (eS:euclidean_orthogonal_group R (1+d)) (theta:set (euclidean_orthogonal_group R (1+d))->\bar R)
    (q : \bar R):
  (d<=k+m)%N ->inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_inv (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_unit (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (euclidean_orthogonal_group R (1+d)) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  let H:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)) in
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  let f:=parameterized_integral (@hausdorff_measure R P ((k+m-d)+d*(d-1)%/2))
    (fun g=>partial_function_zero_extension (0:extended_real_line R)
      [set z|S z /\orthogonal_kinematic_map z=g]
      (real_total_integrand (fun z:P=>alpha (z.1 c)*beta (z.2 c)))) in
  is_measure_integral (measure_restrict (@hausdorff_measure R H ((1+d)*((1+d)-1)%/2))
    [set g|is_orthogonal_map (@euclidean_inner_product R (1+d))
      (@euclidean_inner_product R (1+d)) (hom_as_linear g)]) f q ->
  is_measure_integral theta (spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta)
    (((((Num.sqrt (2:R))^+((k+m-d)+d*(d-1)%/2)*spherical_preimage_mass_scale R d (k+m-d))^-1)%:E)*
      ((stiefel_gamma_volume_scalar R (leqnn (1+d)))^-1)%:E*q)%E.
Proof.
move=>hDim hc hA hB hRA hMA hRB hMB hGroup hTheta H P S f hRaw.
pose G:=euclidean_orthogonal_group R (1+d).
pose om:=@orthogonal_element_map R (R_n R (1+d)) (@euclidean_inner_product R (1+d))
  (@euclidean_inner_productP R (1+d)) (1+d)%N (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)).
pose C:=(Num.sqrt (2:R))^+((k+m-d)+d*(d-1)%/2)*spherical_preimage_mass_scale R d (k+m-d).
pose I:=spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta.
have hC:0<C.
  apply:mulr_gt0; last exact:spherical_preimage_mass_scale_positive.
  apply:exprn_gt0; by rewrite sqrtr_gt0 ltr0n.
have hC0:C!=0 by rewrite gt_eqF.
have hHaar:=@orthogonal_hausdorff_to_haar_integral R (1+d)%N mulS invS eS theta f q hGroup hTheta hRaw.
have hFibres:=@orthogonal_kinematic_coarea_fibres R d k m c A B hDim hc hA hB hRA hMA hRB hMB.
have hGood:=@orthogonal_hausdorff_to_haar_almost R (1+d)%N mulS invS eS theta _ hGroup hTheta hFibres.
have ht:=normalised_haar_measure_law hTheta.
have hBoth:=measure_almost_everywhere_and ht hGood (measurable_function_domain hHaar.1).
have hAlmost:measure_almost_equal theta (partial_function_precompose om f)
    (partial_extended_function_scale C I).
  apply:(measure_almost_everywhere_mono ht _ hBoth)=>g [[hRect hMeas] [z hz]].
  exists z; split; first exact hz.
  pose b:extended_real_line R:=((C^-1)%:E*z)%E.
  have hCancel:(C%:E*b=z)%E by rewrite /b muleA -EFinM mulfV // mul1e.
  have hFibre:=@spherical_kinematic_fibre_integral R d (k+m-d)%N c A B (om g) alpha beta b
    hc hA (orthogonal_element_orthogonal g) hRect hMeas.
  have hSource:is_measure_subset_integral (@hausdorff_measure R P ((k+m-d)+d*(d-1)%/2))
      [set z|S z /\orthogonal_kinematic_map z=om g]
      (real_total_integrand (fun z:P=>alpha (z.1 c)*beta (z.2 c))) (C%:E*b)%E.
    rewrite hCancel.
    exact ((parameterized_integral_specification _ _ _ _).1 hz).
  have hOriginal:=hFibre.2 hSource.
  exists b; split; last exact hCancel.
  exact ((spherical_kinematic_inner_integral_graph _ _ _ _ _ _ _).2 hOriginal).
have hScaled:=measure_integral_almost_equal ht hHaar hAlmost.
have hInverse:=@measure_integral_nonzero_scale R G theta ht C^-1 (partial_extended_function_scale C I)
  (((stiefel_gamma_volume_scalar R (leqnn (1+d)))^-1)%:E*q)%E
  ltac:(by rewrite invr_eq0) hScaled.
have hResult:=measure_integral_graph_equivalent (inverse_scale_graph I hC0) hInverse.
by rewrite muleA in hResult.
Qed.
