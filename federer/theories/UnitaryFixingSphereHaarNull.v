(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),(8),
    pp. 328–330: original unitary coordinate-fixing Haar orbits
    carry coordinate-sphere null sets to null subgroup sets. Reuse
    the proved compact invariant orbit measure and Haar normalization
    comparison, with the original exact isometric coordinate chart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  HermitianUP HermitianRealImaginary HermitianComplexLinearity InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  UnitaryGroup UnitaryComplexMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import HomSpaceTopology TopologicalGroupUP IsotropyGroupTopology TopologicalProductMaps
  SubtypeCompactHausdorff HomogeneousSpaceUP CompactGroupHomogeneousMeasures UnitaryGroupClosed
  UnitaryCoordinateFixing UnitaryCoordinateFixingHaar UnitarySphereTransitivity UnitaryHermitianPreservation.
From Federer Require Import MetricSubsetBackground TopologicalGroupLaws HomogeneousSpaceLaws
  UnitaryFixingSphereAction HausdorffMeasure HausdorffIsometryMeasurability MeasurePushforward.
From Federer Require Import UnitaryFixingSphereInvariant HausdorffClosedCoverAgreement GrassmannAbbreviations EuclideanInnerProduct HaarIntegralUP
  CompactGroupHaarNormalisation CompactMetricInvariantOrbitMeasure IsometricSphereHausdorffTransport
  MeasureUP MeasureScaleIntegral HaarMeasureNullComparison UnitSphereHaarIntegral EulerGamma EulerGammaHalfParameters.
Section Comparison.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Variable N:nat.
Variable r:'I_N->XR.
Variable hr:is_basis r.
Local Notation O:=(@orthogonal_group R XR B hB N r hr).
Local Notation U:=(@unitary_group R X H hH N r hr).
Local Notation L:=(fun g:U=>@UnitaryComplexMap.value R X H hH N r hr g).

Variable n:nat.
Variable e:'I_n->X.
Variable J:set 'I_n.
Local Notation S:=(@unitary_coordinate_fixing_group R X H hH N r hr n e J).
Local Notation XT:=(inner_metric_space hB).
Local Notation HT:=(inner_metric_space (hom_inner_productP hB hB hr)).

Local Notation V:=(@unitary_fixing_sphere R X H hH n e J).
Local Notation M:=([the metricType R of metric_subset V]).
Local Notation A:=(@unitary_fixing_sphere_action R X H hH N r hr n e J).

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB N r hr)
  (@linear_group_inv R XR B hB N r hr) (@linear_group_unit R XR B hB N r hr) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.
Variables (mulS:S->S->S) (invS:S->S) (unitS:S).
Variable hS:is_subgroup_restriction mulU invU unitU S mulS invS unitS.



Variable d:nat.
Variable hPositive:(0<d)%N.
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R d)).
Variable inclusion:Y->XT.
Variable projection:XT->Y.
Variable hLeft:cancel inclusion projection.
Variable hDistance:forall x y,mdist (inclusion x) (inclusion y)=mdist x y.
Variable hImage:inclusion @` [set y:Y|inner_norm (@euclidean_inner_productP R d) y= 1]=V.
Local Notation mass:=(2*(euler_gamma_half R)^+d/euler_gamma (@positive_dimension_half R d hPositive)).

(** Source for [unitary_fixing_sphere_haar_comparison]: the actual
    all-subset Haar/Hausdorff identity on the original complex
    coordinate sphere, 3.4.12, p. 339. *)
Theorem unitary_fixing_sphere_haar_comparison (theta:set S->\bar R) (u:M):
  is_normalised_haar_measure mulS theta ->
  @hausdorff_measure R M (d-1)=measure_scale mass (measure_pushforward (orbit_map A u) theta).
Proof.
move=>hTheta.
have hLocal:=@unitary_fixing_group_lch R X H hH N r hr n e J
  mulO invO unitO hO mulU invU unitU hU mulS invS unitS hS.
have hHomogeneous:=@unitary_fixing_sphere_homogeneous R X H hH N r hr n e J
  mulO invO unitO hO mulU invU unitU hU mulS invS unitS hS.
have hCompact:=@unitary_coordinate_fixing_compact R X H hH N r hr n e J.
have hMass:=@isometric_sphere_hausdorff_mass R XT d inclusion projection V hLeft hDistance hImage hPositive.
have hInvariant:=@unitary_fixing_sphere_hausdorff_invariant R X H hH N r hr n e J
  mulO invO unitO hO mulU invU unitU hU mulS invS unitS hS (d-1)%N.
exact:(@compact_metric_finite_invariant_orbit_measure R S M mulS invS unitS A hLocal hHomogeneous
  (@hausdorff_measure R M (d-1)) theta mass u hCompact
  (@hausdorff_measure_is_measure R M (d-1)) (@hausdorff_measure_borel_regular R M (d-1))
  (@unit_sphere_gamma_mass_positive R d hPositive) hMass hInvariant hTheta).
Qed.

(** Source for [unitary_fixing_sphere_haar_coordinate_null]: every
    original coordinate exceptional set gives a null set of original
    unitary rotations, for every original Haar normalization,
    3.4.12, p. 339. *)
Theorem unitary_fixing_sphere_haar_coordinate_null (mu:set S->\bar R) (u:M) (D:set Y):
  is_left_haar_measure mulS mu ->
  @hausdorff_measure R Y (d-1)
    [set y|inner_norm (@euclidean_inner_productP R d) y= 1 /\D y]=0%:E ->
  mu [set g:S|D (projection (val (A g u)))]=0%:E.
Proof.
move=>hMu hNull.
have hLocal:=@unitary_fixing_group_lch R X H hH N r hr n e J
  mulO invO unitO hO mulU invU unitU hU mulS invS unitS hS.
have hCompact:=@unitary_coordinate_fixing_compact R X H hH N r hr n e J.
have [theta hTheta]:=normalised_haar_measure_exists R hLocal hCompact.
have hComparison:=unitary_fixing_sphere_haar_comparison u hTheta.
pose rho:=measure_pushforward (orbit_map A u) theta.
have hPositiveMass:0<mass:=@unit_sphere_gamma_mass_positive R d hPositive.
have hInverse:measure_scale mass^-1 (@hausdorff_measure R M (d-1))=rho.
  rewrite hComparison;exact:(measure_scale_inverse rho hPositiveMass).
have hSphereNull:=@isometric_sphere_coordinate_null R XT d inclusion projection V hLeft hDistance hImage D hNull.
have hOrbitNull:rho [set v:M|D (projection (val v))]=0%:E.
  by rewrite -hInverse /measure_scale hSphereNull mule0.
have hThetaNull:theta [set g:S|D (projection (val (A g u)))]=0%:E.
  exact:hOrbitNull.
exact:((left_haar_measures_same_null_sets hLocal hMu hTheta.1 _).2 hThetaNull).
Qed.
End Comparison.
