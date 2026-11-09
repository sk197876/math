(** Federer (1969), 3.3.4, pp. 288–289: the original frame
    kernel map sends actual normalized Haar measure to gamma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology OrthogonalGroupTopology GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct
  FiniteCoordinates EuclideanProjectionSpace OrthogonalInjectionSpaces GrassmannHomogeneousSpace
  EuclideanOrthogonalInvariantMeasures EuclideanGrassmannProbability
  EuclideanGrassmannProbabilityUP StructureProjectionKernel StructureKernelEquivariance
  CompactGroupHaarNormalisation HomogeneousSpaceUP MeasurePushforward
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_frame_kernel_probability]: the assertion
    gamma=v#theta in Federer 3.3.4, pp. 288–289, using the independently
    specified actual probabilities and the proved kernel equivariance
    of 3.3.1, p. 287. Every original subset is retained; the auxiliary
    initial projection, group operations and Haar measure stay local. *)
Theorem structure_frame_kernel_probability (R:realType) n m (hmn:(m<=n)%N)
    (mulS:euclidean_orthogonal_group R n->euclidean_orthogonal_group R n->euclidean_orthogonal_group R n)
    (invS:euclidean_orthogonal_group R n->euclidean_orthogonal_group R n)
    (eS:euclidean_orthogonal_group R n)
    (hS:is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (euclidean_orthogonal_group R n) mulS invS eS)
    (theta:set (set_type (euclidean_orthogonal_group R n))->\bar R)
    (p0:euclidean_projection_space R n m):
  is_normalised_haar_measure mulS theta ->
  @measure_pushforward R [the choiceType of set_type (euclidean_orthogonal_group R n)]
    [the choiceType of grassmann_space
      (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
      (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)]
    (fun g=>structure_projection_kernel hmn
    (orthogonal_projection_action (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS g p0)) theta=
  @euclidean_grassmann_probability R n (n-m) (leq_subr m n).
Proof.
move=>hTheta.
have [nu [_ hUnique hOrbit]]:=@euclidean_gamma_nm_exists_unique
  R n (n-m) mulS invS eS hS (leq_subr m n).
rewrite (hUnique _ (@euclidean_grassmann_probability_specification R n (n-m) (leq_subr m n))).
have hImage:=hOrbit theta (structure_projection_kernel hmn p0) hTheta.
rewrite -hImage /measure_pushforward.
apply:funext=>S; congr (theta _); apply:funext=>g; apply:propext.
change (S (structure_projection_kernel hmn
  (orthogonal_projection_action (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS g p0)) <->
  S (grassmann_action (@euclidean_inner_productP R (n-m))
    (@euclidean_inner_productP R n) (@coordinate_basisP R (n-m))
    (@coordinate_basisP R n) g (structure_projection_kernel hmn p0))).
by rewrite (structure_projection_kernel_equivariant hmn hS).
Qed.
