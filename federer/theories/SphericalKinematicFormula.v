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
  SphericalKinematicScalarCancellation SphericalWeightedKinematicInRange SphericalWeightedKinematicNullFactor
  SphericalHigherDegreeNull SphericalKinematicRectifiability SphericalKinematicConstant SphericalKinematicIntegral
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

(** Source for [spherical_weighted_kinematic_formula]: the
    complete weighted equality of 3.2.48, p. 284. All natural
    degrees with k+m>=d, including above-dimensional null factors,
    are retained. Original completed measurable sets, genuinely
    rectifiable B, signed summable weights and the exact original
    inner-integral function occur in the statement. *)
Theorem spherical_weighted_kinematic_formula (R:realType) d k m
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
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_inv (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_unit (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (euclidean_orthogonal_group R (1+d)) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  is_measure_integral theta (spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta)
    (spherical_kinematic_constant R d k m*av*bv)%:E.
Proof.
move=>hDim hA hB hRA hMA hRB hMB hAlpha hBeta hGroup hTheta.
have [hk|hk]:=leqP k d.
- have [hm|hm]:=leqP m d.
  + exact (@spherical_weighted_kinematic_in_range R d k m A B alpha beta av bv mulS invS eS theta
      hk hm hDim hA hB hRA hMA hRB hMB hAlpha hBeta hGroup hTheta).
  + exact (@spherical_weighted_kinematic_null_factor R d k m A B alpha beta av bv mulS invS eS theta
      hDim hA hB hRA hMA hRB hMB hAlpha hBeta
      (or_intror (@spherical_higher_degree_null R d m B hm hB)) hGroup hTheta).
- exact (@spherical_weighted_kinematic_null_factor R d k m A B alpha beta av bv mulS invS eS theta
    hDim hA hB hRA hMA hRB hMB hAlpha hBeta
    (or_introl (@spherical_higher_degree_null R d k A hk hA)) hGroup hTheta).
Qed.

(** Source for [federer_3_2_48]: the entire numbered theorem,
    Federer 3.2.48, p. 284. The original intersections are finitely
    H^lambda rectifiable almost everywhere and their actual weighted
    Haar integral is the printed Gamma coefficient times the two
    original finite signed integrals. Every auxiliary geometric and
    integration premise is proved; no new numbered hypothesis is added. *)
Theorem federer_3_2_48 (R:realType) d k m
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
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_inv (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (linear_group_unit (@euclidean_inner_productP R (1+d)) (@coordinate_basisP R (1+d)))
    (euclidean_orthogonal_group R (1+d)) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  measure_almost_everywhere theta [set g|is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) (k+m-d)) (k+m-d)%N
    (spherical_kinematic_intersection A B g)] /\
  is_measure_integral theta (spherical_kinematic_inner_integral (k+m-d)%N A B alpha beta)
    (spherical_kinematic_constant R d k m*av*bv)%:E.
Proof.
move=>hDim hA hB hRA hMA hRB hMB hAlpha hBeta hGroup hTheta.
split.
- pose c:=spherical_coordinate_pole R d.
  have hc:inner_norm (@euclidean_inner_productP R (1+d)) c= 1.
    exact (@euclidean_coordinate_unit_norm R (1+d)%N (lshift d (ord0:'I_1))).
  exact (@spherical_kinematic_intersection_rectifiable R d k m c A B mulS invS eS theta
    hGroup hTheta hDim hc hA hB hRA hMA hRB hMB).
- exact (@spherical_weighted_kinematic_formula R d k m A B alpha beta av bv mulS invS eS theta
    hDim hA hB hRA hMA hRB hMB hAlpha hBeta hGroup hTheta).
Qed.
