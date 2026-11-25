(** Federer (1969), 3.3.10, p. 296: every original
    Grassmann plane is the kernel of an actual orthogonal projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology GrassmannAbbreviations
  GrassmannSubspaces EuclideanInnerProduct FiniteCoordinates AdjointUP Adjoint
  OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace
  GrassmannHomogeneousSpace StructureProjectionKernel StructureKernelEquivariance
  OrthogonalGroupTopology LinearGroupSealed LinearGroupTopology IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [structure_projection_kernel_onto]: the original
    kernel parametrization used to integrate the fixed-projection
    assertions over G(n,n-m) in Federer 3.3.10, p. 296. Actual
    Grassmann transitivity and the kernel equivariance of 3.3.1,
    p. 287, give existence. All initial projections and group
    operations stay local, including both dimension endpoints. *)
Theorem structure_projection_kernel_onto (R:realType) n m (hmn:(m<=n)%N)
    (V:G (R_n R n) (n-m)):
  exists p:euclidean_projection_space R n m,structure_projection_kernel hmn p=V.
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
have [g hg]:=@grassmann_action_transitive R (R_n R (n-m)) (R_n R n)
  (@euclidean_inner_product R (n-m)) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
  (n-m)%N (@coordinate_basis R (n-m)) n (@coordinate_basis R n)
  (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)
  (structure_projection_kernel hmn p0) V.
exists (orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS g p0).
by rewrite (structure_projection_kernel_equivariant hmn hS).
Qed.
