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
  SphericalKinematicScalarCancellation SphericalKinematicSourceNull SphericalKinematicNullSourceCoarea
  NullMeasureIntegral MeasureIntegralUniqueness SphericalKinematicConstant SphericalKinematicIntegral
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

(** Source for [spherical_weighted_kinematic_null_factor]: the
    zero-equals-zero case explicitly noted in 3.2.48, p. 285.
    Actual original-source nullity, coarea and signed whole-fibre
    changes prove the original Haar integral zero. No above-dimensional
    case or original partial inner-integral domain is discarded. *)
Theorem spherical_weighted_kinematic_null_factor (R:realType) d k m
    (A B:set (R_n R (1+d))) (alpha beta:R_n R (1+d)->R) av bv
    (mulS:euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d))
    (invS:euclidean_orthogonal_group R (1+d)->euclidean_orthogonal_group R (1+d))
    (eS:euclidean_orthogonal_group R (1+d)) (theta:set (euclidean_orthogonal_group R (1+d))->\bar R):
  (d<=k+m)%N ->
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
  ((@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) k A=0)%E \/
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B=0)%E) ->
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_inv (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_unit (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (euclidean_orthogonal_group R (1+d)) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  is_measure_integral theta (spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta)
    (spherical_kinematic_constant R d k m*av*bv)%:E.
Proof.
move=>hDim hA hB hRA hMA hRB hMB hAlpha hBeta hNull hGroup hTheta.
pose c:=spherical_coordinate_pole R d.
have hc:inner_norm (@euclidean_inner_productP R (1+d)) c= 1.
  exact (@euclidean_coordinate_unit_norm R (1+d)%N (lshift d (ord0:'I_1))).
have [a [t hTargetChart]]:=@euclidean_hom_inner_chart_exists R (1+d)%N (1+d)%N.
pose eP:=finite_inner_cartesian_direct a a.
pose pP:=finite_inner_cartesian_inverse t t.
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
have hChart:=finite_inner_cartesian_chart hH hH hTargetChart hTargetChart.
have hNullSource:=@spherical_kinematic_source_null_factor R d k m c A B
  hc hA hB hRA hMA hRB hMB hNull.
have hRaw:=@spherical_kinematic_null_source_coarea R d k m _ _ c A B eP pP a t alpha beta av bv
  hDim hc hA hB hRA hMA hRB hMB hAlpha hBeta hChart hTargetChart hNullSource.
have hNu:=euclidean_skew_dimension_successor d.
rewrite -hNu in hRaw.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)).
pose rho:=@hausdorff_measure R H ((1+d)*((1+d)-1)%/2)%N.
pose O:=[set g:Hom (R_n R (1+d)) (R_n R (1+d))|is_orthogonal_map
  (@euclidean_inner_product R (1+d)) (@euclidean_inner_product R (1+d)) (hom_as_linear g)].
have hTarget:=@orthogonal_group_measure_rectifiable R (1+d)%N.
have hRestricted:=(@restricted_integral_zero_extension_iff R H rho
  (@hausdorff_measure_is_measure R H ((1+d)*((1+d)-1)%/2)%N) O _ _ hTarget.2).2 hRaw.
have hOuter:=@spherical_kinematic_outer_integral R d k m c A B alpha beta mulS invS eS theta 0%E
  hDim hc hA hB hRA hMA hRB hMB hGroup hTheta hRestricted.
rewrite !mule0 in hOuter.
pose X:=inner_metric_space (@euclidean_inner_productP R (1+d)).
case:hNull=>hNull.
- pose HA:=@hausdorff_measure R X k.
  have hTotal:(measure_restrict HA A setT=0)%E by rewrite /measure_restrict setIT.
  have hZero:=@null_whole_measure_integral R X (measure_restrict HA A)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R X k) A) (real_total_integrand alpha) hTotal.
  have hAV:av=0%R:=EFin_inj (measure_integral_unique hAlpha hZero).
  rewrite hAV mulr0 mul0r; exact hOuter.
- pose HB:=@hausdorff_measure R X m.
  have hTotal:(measure_restrict HB B setT=0)%E by rewrite /measure_restrict setIT.
  have hZero:=@null_whole_measure_integral R X (measure_restrict HB B)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R X m) B) (real_total_integrand beta) hTotal.
  have hBV:bv=0%R:=EFin_inj (measure_integral_unique hBeta hZero).
  rewrite hBV mulr0; exact hOuter.
Qed.
