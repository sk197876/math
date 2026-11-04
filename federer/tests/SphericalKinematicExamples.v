(** Federer (1969), 3.2.48, p. 284: concrete regressions
    retain both atoms of the actual one-dimensional sphere, signed
    nonzero weights, and the half-probability of one singleton
    intersection under the actual normalized orthogonal Haar measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology ring.
From Federer Require Import
  OrthogonalKinematicMap OrthogonalKinematicTangent OrthogonalKinematicFibres OrthogonalKinematicFibreScale SphericalMeasurablePullback
  SphericalFinitePullback SphericalPullbackPushforward SphericalWeightedPullback SphericalKinematicConstant SubspaceBorelRegularMeasure
  RectifiableCompletedCartesianProduct OrthogonalKinematicLipschitz OrthogonalKinematicIsometries OrthogonalGroupHausdorffCarrier OrthogonalGroupHausdorffVolume
  OrthogonalGroupHausdorffInvariance OrthogonalGroupHaarBridge SphericalKinematicIntegral SphericalOrthogonalGroupVolume FiniteInnerChartMeasureTransport
  CartesianExteriorWordNorm CartesianTopExteriorNorm OrthogonalHausdorffHaarTransport FiniteInnerChartMeasuredImages FiniteInnerCoareaFibres
  HodgeUnitSimpleFactor FiniteInnerCartesianChart HausdorffIsometryMeasurability FiniteInnerCompletedCartesianProduct HodgeWedgeHaarAverage
  OrthogonalKinematicDimensions SphericalKinematicSource OrthogonalHausdorffHaarAlmost OrthogonalKinematicCoareaFibres OrthogonalKinematicFibreProjection
  SphericalKinematicRectifiability CartesianDifferenceExteriorNorm ExteriorIsometricPrecomposition SphericalTangentOrthogonalSplit InjectiveRestrictionPushforward
  FiniteInnerCompletedCartesianMeasure HausdorffSimilarityEmbedding HausdorffSimilarityRestriction SphericalWeightedPreimageTransport SphericalPreimageConverseMeasurable
  OrthogonalKinematicFibreMeasurability SphericalKinematicFibreIntegrals SphericalVerticalTangentPlane SphericalTangentCartesianChart SphericalHorizontalTranslation
  CartesianFourFactorShuffle CommonVerticalDifferenceExteriorNorm GrassmannSimpleUnitRepresentative SphericalTangentCoordinates SphericalIsotropyTransverseAction
  SubmanifoldSubsetVariableJacobian GrassmannInjectiveImageOn SphericalTranslatedTangentPlane SphericalTranslatedCartesianChart SphericalTranslatedTangentEquations
  SphericalPreimageIsometricChart SphericalKinematicTargetEmbedding SphericalKinematicDifferentialDiagram SphericalKinematicChartJacobian InnerCartesianRetractionTangent
  FiniteInnerCartesianSubmanifoldTangents SphericalKinematicManifoldJacobian SphericalKinematicSourceWeights InnerCartesianCoordinateSystems FiniteInnerCoordinateParameterChart
  FiniteInnerCartesianSubmanifold GrassmannCartesianProduct FiniteInnerCartesianTangentJacobian OrthogonalKinematicDifferential EuclideanTangentExteriorNorm
  SubmanifoldSubsetIntrinsicJacobian OrthogonalKinematicCoordinateDifferential SphericalKinematicTangentProfile SphericalKinematicApproximateProfile HodgeWedgeAssociatedPlanes
  SphericalKinematicTangentWordFormula AssociatedSubspaceIsomorphism HodgeOrthogonalTransport SphericalIsotropyTangentWords SphericalKinematicProfileIsotropy
  SphericalKinematicProfileHaarAverage SphericalPreimageRightInvariance InvariantProbabilityAverage InnerCartesianContinuousMaps SphericalIsotropyActionContinuity
  MeasureScaleBorelRegular OrthogonalCartesianRightInvariance OrthogonalHaarRegularity InvariantProbabilityAverageIntegral SphericalKinematicSourceAverage
  FiniteInnerIntegralCoordinates RectifiableCoareaVariableProfile RectifiableWeightedCoareaProfile FiniteInnerWeightedCoareaProfile InvariantProbabilityOrbitIntegral
  SphericalKinematicManifoldCoarea SphericalKinematicManifoldAverage SphericalKinematicOuterIntegral DifferentiableSubsetJacobianAgreement DisjointFamilySelector
  SphericalRectifiablePartition CountableDifferentiableJacobianProfile SphericalKinematicCoverAlmost SphericalKinematicPartitionProfile SphericalKinematicMeasurablePiece
  SphericalKinematicPartitionApproximate SphericalKinematicPartitionCoarea SphericalKinematicScalarCancellation SphericalKinematicPartitionAverage SphericalWeightedKinematicInRange
  NullMeasureIntegral SphericalKinematicSourceNull SphericalHigherDegreeNull SphericalKinematicNullSourceCoarea SphericalWeightedKinematicNullFactor
  SphericalKinematicFormula.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  FiniteCoordinates CoordinateProjection EuclideanOneNormDifferential EuclideanOneCoordinate
  EuclideanHomInnerCharts OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HomSpaceTopology TopologicalGroupUP
  HaarIntegralUP CompactGroupHaarNormalisation UnitSphereSpace EuclideanSphereMeasurable
  HausdorffMeasure HausdorffUnitSphereMass HausdorffCountingMeasure EuclideanBallVolume EuclideanUnitSphereRectifiable
  RectifiableSetUP RectifiableElementary RectifiableFiniteHausdorffMass FiniteExceptionalBorel
  HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel GammaHalfSequences EulerGamma EulerGammaHalfParameters
  MeasureUP MeasureRestriction MeasureIntegralUP MeasureStepConstants MeasureStepIntegralIdentification
  SummableRealFunctionUP SphericalKinematicFormula SphericalKinematicIntegral SphericalKinematicConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kinematic_zero_sphere_constant]: the Gamma coefficient
    of 3.2.48, p. 284, is one half when n= 1 and k=m=0.
    Actual positive Euler Gamma factors cancel; no coefficient is assigned. *)
Lemma kinematic_zero_sphere_constant (R:realType):
  spherical_kinematic_constant R 0 0 0= 1/2.
Proof.
pose g:=euler_gamma_half R.
have hg:g!=0:=lt0r_neq0 (euler_gamma_positive _).
rewrite /spherical_kinematic_constant !gamma_half_sequence_zero expr1.
change (g*g/(2*g*g)= 1/2).
have hDen:2*g*g= 2*(g*g) by ring.
have hGG:g*g!=0:=mulf_neq0 hg hg.
rewrite hDen invfM.
have hReorder:(g*g)*(2^-1*(g*g)^-1)= 2^-1*((g*g)*(g*g)^-1) by ring.
by rewrite hReorder mulfV // mulr1 div1r.
Qed.

(** Source for [kinematic_real_constant_integral]: constant signed
    weights in the actual regressions for 3.2.48, p. 284, by
    the step integral of 2.4.1, p. 80. Infinite masses and
    negative constants keep the existing multiplication convention. *)
Lemma kinematic_real_constant_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (c:R):
  is_measure_integral mu (real_total_integrand (fun _=>c)) (c%:E*mu setT)%E.
Proof.
exact (@measure_step_function_integral R X mu hm _ _ (measure_step_constant hm c)
  (measure_step_constant_integral hm c)).
Qed.

Section ActualOrthogonalHaar.
Variable R:realType.
Variables (mulS:euclidean_orthogonal_group R 1->euclidean_orthogonal_group R 1->euclidean_orthogonal_group R 1)
  (invS:euclidean_orthogonal_group R 1->euclidean_orthogonal_group R 1)
  (eS:euclidean_orthogonal_group R 1) (theta:set (euclidean_orthogonal_group R 1)->\bar R).
Hypothesis hGroup:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R 1) (@coordinate_basisP R 1))
  (linear_group_inv (@euclidean_inner_productP R 1) (@coordinate_basisP R 1))
  (linear_group_unit (@euclidean_inner_productP R 1) (@coordinate_basisP R 1))
  (euclidean_orthogonal_group R 1) mulS invS eS.
Hypothesis hTheta:is_normalised_haar_measure mulS theta.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R 1)).
Local Notation H:=(@hausdorff_measure R X 0).
Local Notation S:=(@euclidean_unit_sphere_set R 1).

(** Source for [kinematic_actual_two_sphere_atoms]: the positive
    whole-source test for 3.2.48, p. 284. The actual S^0 has
    mass two; this premise is derived from the unit sphere mass theorem. *)
Lemma kinematic_actual_two_sphere_atoms:H S= 2%E.
Proof.
have h:=@hausdorff_unit_sphere_mass R 1 (ltnSn 0).
by rewrite euclidean_unit_ball_volume1 mul1r in h.
Qed.

(** Source for [kinematic_full_zero_sphere_weights]: a concrete
    signed constant-weight instance of the full 3.2.48 formula,
    p. 284, on the actual two-point sphere. Both source masses
    are two, so the finite integral is nonzero for unit weights. *)
Lemma kinematic_full_zero_sphere_weights (a b:R):
  is_measure_integral theta (spherical_kinematic_inner_integral 0 S S
    (fun _=>a) (fun _=>b)) (2*a*b)%:E.
Proof.
have hRect:@is_m_rectifiable R X 0 S:=@euclidean_unit_sphere_rectifiable R 1.
have hFinite:=rectifiable_hausdorff_measure_rectifiable hRect.
have hMeas:measure_measurable H S:=@euclidean_norm_sphere_hausdorff_measurable R 1 0 1.
have hA:=kinematic_real_constant_integral (measure_restrict_is_measure (@hausdorff_measure_is_measure R X 0) S) a.
have hB:=kinematic_real_constant_integral (measure_restrict_is_measure (@hausdorff_measure_is_measure R X 0) S) b.
rewrite /measure_restrict setIT kinematic_actual_two_sphere_atoms -EFinM in hA hB.
have h:=(@federer_3_2_48 R 0 0 0 S S (fun _=>a) (fun _=>b) (a*2) (b*2)
  mulS invS eS theta (leqnn 0) (fun x hx=>hx) (fun x hx=>hx)
  hFinite hMeas hRect hMeas hA hB hGroup hTheta).2.
rewrite kinematic_zero_sphere_constant in h.
have hValue:(1/2:R)*(a*2)*(b*2)= 2*a*b by field.
by rewrite hValue in h.
Qed.

(** Source for [spherical_kinematic_two_atom_example]: actual
    positive-mass boundary regression for 3.2.48, p. 284:
    the average intersection mass of the whole S^0 with itself is two. *)
Example spherical_kinematic_two_atom_example:
  H S= 2%E /\is_measure_integral theta
    (spherical_kinematic_inner_integral 0 S S (fun _=>1) (fun _=>1)) 2%E.
Proof.
split; first exact kinematic_actual_two_sphere_atoms.
have h:=kinematic_full_zero_sphere_weights (1:R) (1:R).
by rewrite !mulr1 in h.
Qed.

(** Source for [spherical_kinematic_signed_two_atom_example]: the
    signed, nonzero regression for 3.2.48, p. 284: alpha=-1,
    beta= 1 on the actual two-point sphere gives average integral -2. *)
Example spherical_kinematic_signed_two_atom_example:
  H S= 2%E /\is_measure_integral theta
    (spherical_kinematic_inner_integral 0 S S (fun _=> -1) (fun _=>1)) (-2)%:E.
Proof.
split; first exact kinematic_actual_two_sphere_atoms.
have h:=kinematic_full_zero_sphere_weights (-1:R) (1:R).
by rewrite mulrN1 mulr1 in h.
Qed.

(** Source for [spherical_kinematic_singleton_example]: the
    positive-atom singleton regression for 3.2.48, p. 284.
    A=B={1} each has actual H^0 mass one; its original
    intersection integral has actual normalized Haar average one half. *)
Example spherical_kinematic_singleton_example:
  let c:=euclidean_one_embed (1:R) in
  H [set c]= 1%E /\is_measure_integral theta
    (spherical_kinematic_inner_integral 0 [set c] [set c] (fun _=>1) (fun _=>1)) (1/2:R)%:E.
Proof.
move=>c.
have hMass:H [set c]= 1%E:=hausdorff_zero_singleton c.
have hc:inner_norm (@euclidean_inner_productP R 1) c= 1.
  by rewrite /c euclidean_one_norm_coordinate /euclidean_one_embed ffunE normr1.
have hInside:[set c] `<=` S by move=>x ->; exact hc.
have hRect:@is_m_rectifiable R X 0 [set c]:=(@zero_rectifiable_finite R X [set c]).2 (finite_set1 c).
have hFinite:=rectifiable_hausdorff_measure_rectifiable hRect.
have hMeas:measure_measurable H [set c].
  exact (borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 0)
    (@hausdorff_measure_borel_regular R X 0) (finite_metric_set_borel (finite_set1 c))).
have hOne:=kinematic_real_constant_integral
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R X 0) [set c]) (1:R).
rewrite /measure_restrict setIT hMass mul1e in hOne.
have h:=(@federer_3_2_48 R 0 0 0 [set c] [set c] (fun _=>1) (fun _=>1) 1 1
  mulS invS eS theta (leqnn 0) hInside hInside hFinite hMeas hRect hMeas hOne hOne hGroup hTheta).2.
rewrite kinematic_zero_sphere_constant !mulr1 in h.
by split.
Qed.
End ActualOrthogonalHaar.
