(** Federer (1969), 3.2.48, p. 286: averaging the exact original
    source measure over the actual right isotropy action preserves it.
    Every regularity, finiteness, continuity and invariance requirement
    is proved from the printed rectifiability/measurability hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal topology subtype_topology ring.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  LinearBasis HomCompositionDeterminant EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  EuclideanHomInnerCharts HomInner HomSpaceTopology ProductInner ProductFiniteBasis InnerSpaceCountableBase
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology TopologicalGroupUP
  HaarIntegralUP CompactGroupHaarNormalisation OrthogonalHaarRegularity
  SphericalIsotropyTransverseAction SphericalCoordinateIsotropy SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalKinematicSource OrthogonalCartesianRightInvariance
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse UnitSphereSpace OrthogonalMaps
  RectifiableSetUP HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureRestriction
  MeasurePushforward ProductMeasure BorelRegularMeasureUP BorelRegularFiniteRestriction InvariantProbabilityAverage
  SphericalKinematicSourceAverage SphericalKinematicProfileHaarAverage SphericalKinematicTangentProfile
  SphericalKinematicSourceWeights InvariantProbabilityOrbitIntegral
  SphericalRectifiablePartition DisjointFamilySelector SphericalKinematicPartitionProfile SphericalKinematicCoverAlmost SphericalTangentCoordinates
  EuclideanLinearMaps FiniteInnerChartUP SphericalPullbackPushforward ExteriorGrading ExteriorNorm HilbertFormCompactness EuclideanSubmanifoldUP GammaHalfSequences
  MeasureIntegralUP MeasureAlmostUP MeasureAlmostBasic MeasureBasic RestrictedAlmostEverywhere
  SummableRealFunctionUP SummableRealArithmetic
  SphericalKinematicPartitionAverage SphericalKinematicPartitionCoarea SphericalKinematicOuterIntegral
  SphericalKinematicScalarCancellation SphericalKinematicConstant SphericalKinematicIntegral
  SphericalRectifiablePartition DisjointFamilySelector SphericalTangentCoordinates
  FiniteInnerCartesianChart FiniteInnerChartUP OrthogonalKinematicCoareaFibres
  EuclideanStiefelVolumeDimensions FiniteExteriorPowers ExteriorFrameUnitNorm
  EuclideanCoordinateMetric RectifiableFiniteHausdorffMass RestrictedIntegralIdentity
  OrthogonalKinematicMap PartialZeroExtension ParameterizedIntegral StiefelGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_weighted_kinematic_in_range]: the
    weighted equality of 3.2.48, p. 284, when k,m do not exceed
    the sphere dimension. All auxiliary poles, frames, charts,
    partitions, selectors, tangent words and isotropy Haar measures
    are obtained locally from their proved public laws. Original
    completed measurable A,B and signed summable weights remain. *)
Theorem spherical_weighted_kinematic_in_range (R:realType) d k m
    (A B:set (R_n R (1+d))) (alpha beta:R_n R (1+d)->R) av bv
    (mulS:euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d))
    (invS:euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d))
    (eS:euclidean_orthogonal_group R (1+d)) (theta:set (euclidean_orthogonal_group R (1+d))->\bar R):
  (k<=d)%N ->(m<=d)%N ->(d<=k+m)%N ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A) (real_total_integrand alpha) av%:E ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B) (real_total_integrand beta) bv%:E ->
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_inv (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_unit (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (euclidean_orthogonal_group R (1+d)) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  is_measure_integral theta (spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta)
    (spherical_kinematic_constant R d k m*av*bv)%:E.
Proof.
move=>hk hm hDim hA hB hRA hMA hRB hMB hAlpha hBeta hGroup hTheta.
pose c:=spherical_coordinate_pole R d.
have hc:inner_norm (@euclidean_inner_productP R (1+d)) c= 1.
  exact (@euclidean_coordinate_unit_norm R (1+d)%N (lshift d (ord0:'I_1))).
have [Q [hQ hQc]]:=spherical_transverse_frame_exists hc.
have [CA [M hCA]]:=@spherical_rectifiable_partition_exists R d k A hA hRA.
have [CB [N hCB]]:=@spherical_rectifiable_partition_exists R d m B hB
  (rectifiable_hausdorff_measure_rectifiable hRB).
have [sA hSelectA]:=disjoint_family_selector_exists (spherical_partition_disjoint hCA).
have [sB hSelectB]:=disjoint_family_selector_exists (spherical_partition_disjoint hCB).
have [a [t hTargetChart]]:=@euclidean_hom_inner_chart_exists R (1+d)%N (1+d)%N.
pose eP:=finite_inner_cartesian_direct a a.
pose pP:=finite_inner_cartesian_inverse t t.
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
have hChart:=finite_inner_cartesian_chart hH hH hTargetChart hTargetChart.
have ht:=finite_inner_chart_inverse_product hTargetChart.
pose E:=e_lambda (@coordinate_basis R d) (ord_tuple d).
have hE:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E= 1.
  exact (@euclidean_top_product_unit_norm R (euclidean_two_nonzero R) d).
have [mulD [invD [eD hGroupD]]]:=@orthogonal_group_restriction_exists R (R_n R d) _
  (@euclidean_inner_productP R d) d (@coordinate_basis R d) (@coordinate_basisP R d).
have [thetaD hThetaD]:=@orthogonal_normalised_haar_measure_exists R (R_n R d) _
  (@euclidean_inner_productP R d) d (@coordinate_basis R d) (@coordinate_basisP R d) mulD invD eD hGroupD.
have [q [hSource hRaw]]:=@spherical_kinematic_partition_coarea R d k m _ _ c A B CA CB M N sA sB
  eP pP a t alpha beta av bv hDim hc hA hB hRA hMA hRB hMB hAlpha hBeta
  hCA hCB hSelectA hSelectB hChart hTargetChart.
have hValue:=@spherical_kinematic_partition_average R d k m hk hm hDim c Q A B CA CB M N sA sB E
  _ _ eP pP t alpha beta av bv mulD invD eD thetaD hc hQ hQc hA hB hRA hMA hRB hMB hAlpha hBeta
  hCA hCB hSelectA hSelectB hE hChart ht hGroupD hThetaD q hSource.
rewrite hValue in hRaw.
have hNu:=euclidean_skew_dimension_successor d.
rewrite -hNu in hRaw.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)).
pose rho:=@hausdorff_measure R H ((1+d)*((1+d)-1)%/2)%N.
pose O:=[set g:Hom (R_n R (1+d)) (R_n R (1+d))|is_orthogonal_map
  (@euclidean_inner_product R (1+d)) (@euclidean_inner_product R (1+d)) (hom_as_linear g)].
have hTarget:=@orthogonal_group_measure_rectifiable R (1+d)%N.
have hRestricted:=(@restricted_integral_zero_extension_iff R H rho
  (@hausdorff_measure_is_measure R H ((1+d)*((1+d)-1)%/2)%N) O _ _ hTarget.2).2 hRaw.
have hOuter:=@spherical_kinematic_outer_integral R d k m c A B alpha beta mulS invS eS theta _
  hDim hc hA hB hRA hMA hRB hMB hGroup hTheta hRestricted.
rewrite -!EFinM in hOuter.
pose C:=(Num.sqrt (2:R))^+((k+m-d)+d*(d-1)%/2)*spherical_preimage_mass_scale R d (k+m-d).
pose V:=stiefel_gamma_volume_scalar R (leqnn (1+d)).
pose J:=(Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d))*
  (gamma_half_sequence R k*gamma_half_sequence R m/
    (gamma_half_sequence R d*gamma_half_sequence R (k+m-d))).
have hCoefficient:C^-1*V^-1*(J*((spherical_preimage_mass_scale R d k*av)*
      (spherical_preimage_mass_scale R d m*bv)))=spherical_kinematic_constant R d k m*av*bv.
  have hReorder:C^-1*V^-1*(J*((spherical_preimage_mass_scale R d k*av)*
      (spherical_preimage_mass_scale R d m*bv)))=
      (C^-1*V^-1*(J*(spherical_preimage_mass_scale R d k*spherical_preimage_mass_scale R d m)))*av*bv by ring.
  rewrite hReorder (@spherical_kinematic_scalar_cancellation R d k m c hDim hc); reflexivity.
change (is_measure_integral theta (spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta)
  (C^-1*V^-1*(J*((spherical_preimage_mass_scale R d k*av)*(spherical_preimage_mass_scale R d m*bv))))%:E) in hOuter.
by rewrite hCoefficient in hOuter.
Qed.
