(** Federer (1969), 3.3.1, p. 287: the original projection-kernel
    map is continuous and open. Equivariance and the already proved
    homogeneous orbit laws discharge both assertions. All auxiliary
    group operations and a base projection remain local to the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates AdjointUP Adjoint OrthogonalGroupTopology
  OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  EuclideanProjectionSpace GrassmannHomogeneousSpace HomogeneousSpaceUP
  HomeomorphismUP HomogeneousEquivariantContinuous HomogeneousEquivariantOpen
  StructureProjectionKernel StructureKernelEquivariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [structure_projection_kernel_continuous_open]: the
    final sentence of Federer 3.3.1, p. 287: p maps continuously
    and openly to ker p in G(n,n-m). No chosen frame, continuity
    assumption or compactness substitute occurs in the statement. *)
Theorem structure_projection_kernel_continuous_open (R:realType) n m
    (hmn:(m<=n)%N):
  continuous (fun p:euclidean_projection_space R n m=>
    (structure_projection_kernel hmn p:grassmann_space
      (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
      (@coordinate_basisP R (n-m)) (@coordinate_basisP R n))) /\
  @is_open_map (euclidean_projection_space R n m)
    [the topologicalType of grassmann_space
      (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
      (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)]
    (@structure_projection_kernel R n m hmn).
Proof.
have [mulS [invS [eS hS]]]:=orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [f hf]:=@euclidean_orthogonal_injection_exists R n m hmn.
have hp:is_orthogonal_projection (@euclidean_inner_product R n)
    (@euclidean_inner_product R m)
    (inner_adjoint (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R n) (@coordinate_basisP R m) f).
  by exists f; split; [exact:hf|exact:inner_adjointP].
pose p0:=orthogonal_projection_of (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hp.
have hA:=orthogonal_projections_homogeneous (@euclidean_inner_productP R m)
  (@coordinate_basisP R m) hS.
have hB:=@grassmann_space_homogeneous R (R_n R (n-m)) (R_n R n)
  (@euclidean_inner_product R (n-m)) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
  (n-m)%N (@coordinate_basis R (n-m)) n (@coordinate_basis R n)
  (@coordinate_basisP R (n-m)) (@coordinate_basisP R n) mulS invS eS hS.
have hEq:=@structure_projection_kernel_equivariant R n m hmn mulS invS eS hS.
split.
- exact:(homogeneous_equivariant_continuous_map p0 hA hB hEq).
- exact:(homogeneous_equivariant_open_map p0 hA hB hEq).
Qed.
