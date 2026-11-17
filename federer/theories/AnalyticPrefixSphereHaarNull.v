(** Federer (1969), 3.4.8(6), pp. 328–329:
    the original Haar orbit carries coordinate-null
    direction sets to null exceptional subgroup sets.
    Any original Haar normalization is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct HomInner
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed TopologicalGroupUP IsotropyGroupTopology
  HomogeneousSpaceUP HaarIntegralUP CompactGroupHaarNormalisation CompactMetricInvariantOrbitMeasure
  MetricSubsetBackground HausdorffMeasure HausdorffClosedCoverAgreement MeasureScaleIntegral MeasurePushforward
  AnalyticPrefixCoordinatesUP OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar
  AnalyticPrefixSphereAction AnalyticPrefixSphereMeasureInvariant AnalyticPrefixSphereHausdorffMass
  UnitSphereHaarIntegral EulerGamma EulerGammaHalfParameters AnalyticPrefixSphereHaarComparison
  AnalyticPrefixSphereNullTransport HaarMeasureNullComparison.
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

(** Source for [analytic_prefix_sphere_haar_coordinate_null]:
    the actual exceptional-direction transport in the
    proof of 3.4.8(6), pp. 328–329. Positive sphere
    mass and Haar normalization independence are proved
    before this implication is used. *)
Theorem analytic_prefix_sphere_haar_coordinate_null (mu:set H->\bar R) (u:M) (D:set (R_n R p)):
  is_left_haar_measure mulH mu ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R p)) (p-1)
    [set y|inner_norm (@euclidean_inner_productP R p) y = 1 /\D y] = 0%E ->
  mu [set h:H|D (P (@orthogonal_element_map R X B hB n e he (set_val h) (val u)))] = 0%E.
Proof.
move=>hMu hNull.
have hLCH:=@orthogonal_coordinate_fixing_lch R X B hB n e he [set i:'I_n|(p<=i)%N]
  mulO invO unitO hO mulH invH unitH hH.
have [theta hTheta]:=@orthogonal_coordinate_fixing_haar_exists R X B hB n e he
  [set i:'I_n|(p<=i)%N] mulO invO unitO hO mulH invH unitH hH.
have hComparison:=@analytic_prefix_sphere_haar_comparison R X B hB n e he hON omega hDual
  p hPN hPositive P S hP hS mulO invO unitO hO mulH invH unitH hH theta u hTheta.
pose C:=2*(euler_gamma_half R)^+p/euler_gamma (@positive_dimension_half R p hPositive).
pose rho:=measure_pushforward (orbit_map A u) theta.
have hPositiveC:0<C:=@unit_sphere_gamma_mass_positive R p hPositive.
have hInverse:measure_scale C^-1 (@hausdorff_measure R M (p-1)) = rho.
  rewrite hComparison;exact:(measure_scale_inverse rho hPositiveC).
have hSphereNull:=@analytic_prefix_sphere_coordinate_null R X B hB n e he hON omega hDual
  p hPN P S hP hS D hNull.
have hOrbitNull:rho [set v:M|D (P (val v))] = 0%E.
  by rewrite -hInverse /measure_scale hSphereNull mule0.
have hThetaNull:theta [set h:H|D (P (@orthogonal_element_map R X B hB n e he (set_val h) (val u)))] = 0%E.
  exact:hOrbitNull.
exact:((left_haar_measures_same_null_sets hLCH hMu hTheta.1 _).2 hThetaNull).
Qed.
End Comparison.
