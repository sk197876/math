(** Federer (1969), 3.3.4, pp. 288–292: the complete original
    almost-everywhere trichotomy in positive codimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom HomInner HomSpaceTopology GrassmannHomogeneousSpace GrassmannAbbreviations GrassmannSubspaces
  FiniteCoordinates EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanBlockLinearMaps StructureCoordinateProjection OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation
  EuclideanGrassmannProbability StructurePlaneGrowth StructureConeUP StructureFrameTrichotomy
  StructureFrameKernelProbability StructureProjectionKernel MeasurePushforward MeasureAlmostUP SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_trichotomy_positive_codimension]: Federer
    3.3.4, pp. 288–292, all three printed alternatives for actual
    gamma_(n,n-m)-almost every original plane, with n=m+k and k>0.
    The actual first-block projection and actual normalized Haar measure
    are local existence witnesses only. The proved Haar-frame trichotomy
    and exact all-set Grassmann pushforward discharge the conclusion.
    The original Suslin source and closed-measurable outer measure need
    no finiteness, Borel regularity, density or selected-frame hypothesis. *)
Theorem structure_trichotomy_positive_codimension (R:realType) m k (hmn:(m<=m+k)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k))):
  (0<k)%N ->is_structure_measure phi ->is_suslin_set R A ->
  @measure_almost_everywhere R
    [the choiceType of grassmann_space
      (@euclidean_inner_productP R ((m+k)-m)) (@euclidean_inner_productP R (m+k))
      (@coordinate_basisP R ((m+k)-m)) (@coordinate_basisP R (m+k))]
    (@euclidean_grassmann_probability R (m+k) ((m+k)-m) (leq_subr m (m+k)))
    [set V|structure_plane_trichotomy m phi A a V].
Proof.
move=>hk hPhi hA.
have [p0 hP0]:=euclidean_projection_linear_complete (@structure_first_block_projection_orthogonal R m k).
have [mulS [invS [eS hS]]]:=@orthogonal_group_restriction_exists R (R_n R (m+k))
  (@euclidean_inner_product R (m+k)) (@euclidean_inner_productP R (m+k))
  (m+k) (@coordinate_basis R (m+k)) (@coordinate_basisP R (m+k)).
have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R (R_n R (m+k))
  (@euclidean_inner_product R (m+k)) (@euclidean_inner_productP R (m+k))
  (m+k) (@coordinate_basis R (m+k)) (@coordinate_basisP R (m+k)) mulS invS eS hS.
have hImage:=@structure_frame_kernel_probability R (m+k) m hmn mulS invS eS hS theta p0 hTheta.
rewrite -hImage /measure_almost_everywhere /measure_pushforward.
exact:(@structure_frame_almost_everywhere_trichotomy R m k hmn mulS invS eS hS
  theta p0 hP0 phi A a hk hPhi hA hTheta).
Qed.
