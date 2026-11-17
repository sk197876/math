(** Federer (1969), 3.4.8(6), p. 328:
    actual Haar orbit measure on the prefix sphere
    is proportional to its Hausdorff measure.
    The original coordinate equations discharge the
    reference measure's finite positive mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct HomInner
  OrthogonalGroupTopology LinearGroupTopology LinearGroupSealed TopologicalGroupUP IsotropyGroupTopology
  HomogeneousSpaceUP HaarIntegralUP CompactGroupHaarNormalisation CompactMetricInvariantOrbitMeasure
  MetricSubsetBackground HausdorffMeasure HausdorffClosedCoverAgreement MeasureScaleIntegral MeasurePushforward
  AnalyticPrefixCoordinatesUP OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar
  AnalyticPrefixSphereAction AnalyticPrefixSphereMeasureInvariant AnalyticPrefixSphereHausdorffMass
  UnitSphereHaarIntegral EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Comparison.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Variable p:nat.
Variable hPN:(p<=n)%N.
Variable hPositive:(0<p)%N.
Variable P:Hom X (R_n R p).
Variable S:Hom (R_n R p) X.
Hypothesis hP:is_analytic_prefix_projection omega hPN P.
Hypothesis hS:is_analytic_prefix_section e hPN S.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation H:=(@analytic_prefix_rotation_group R X B hB n e he p).
Local Notation sphere:=(@analytic_prefix_unit_sphere R X B hB n e p).
Local Notation M:=([the metricType R of metric_subset sphere]).
Local Notation A:=(@analytic_prefix_sphere_action R X B hB n e he p).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_prefix_sphere_haar_comparison]: the
    actual all-subset identity asserting that the
    orbit image of Haar measure is a constant
    multiple of H^(p-1) on S,
    3.4.8(6), p. 328. No measure-comparison
    conclusion or regular-direction premise is assumed. *)
Theorem analytic_prefix_sphere_haar_comparison (theta:set H->\bar R) (u:M):
  is_normalised_haar_measure mulH theta ->
  @hausdorff_measure R M (p-1) = measure_scale
    (2*(euler_gamma_half R)^+p/euler_gamma (@positive_dimension_half R p hPositive))
    (measure_pushforward (orbit_map A u) theta).
Proof.
move=>hTheta.
have hLCH:=@orthogonal_coordinate_fixing_lch R X B hB n e he [set i:'I_n|(p<=i)%N]
  mulO invO unitO hO mulH invH unitH hH.
have hHomogeneous:=@analytic_prefix_sphere_homogeneous R X B hB n e he p
  mulO invO unitO hO mulH invH unitH hH hON hPN.
have hCompact:=@orthogonal_coordinate_fixing_compact R X B hB n e he [set i:'I_n|(p<=i)%N].
have hMass:=@analytic_prefix_sphere_hausdorff_mass R X B hB n e he hON omega hDual p hPN P S hP hS hPositive.
have hInvariant:=@analytic_prefix_sphere_hausdorff_invariant R X B hB n e he p
  mulO invO unitO hO mulH invH unitH hH hON hPN.
exact:(@compact_metric_finite_invariant_orbit_measure R H M mulH invH unitH A hLCH hHomogeneous
  (@hausdorff_measure R M (p-1)) theta
  (2*(euler_gamma_half R)^+p/euler_gamma (@positive_dimension_half R p hPositive)) u
  hCompact (@hausdorff_measure_is_measure R M (p-1)) (@hausdorff_measure_borel_regular R M (p-1))
  (@unit_sphere_gamma_mass_positive R p hPositive) hMass hInvariant hTheta).
Qed.
End Comparison.
