(** Sealed kernel-plane object for Federer (1969), 3.3.1,
    p. 287. Only its independent annihilation laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanProjectionSpace StructureProjectionKernelUP StructureProjectionKernelConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type StructureProjectionKernelSignature.
(** Source for [value]: the actual kernel plane of a member
    of O*(n,m), Federer 3.3.1, p. 287. *)
Parameter value:forall (R:realType) n m,(m<=n)%N ->
  euclidean_projection_space R n m ->G (R_n R n) (n-m).
(** Source for [laws]: the annihilation membership laws of
    ker p in Federer 3.3.1, p. 287. *)
Parameter laws:forall (R:realType) n m (hmn:(m<=n)%N)
  (p:euclidean_projection_space R n m),
  is_structure_projection_kernel p (@value R n m hmn p).
End StructureProjectionKernelSignature.

Module StructureProjectionKernel:StructureProjectionKernelSignature.
(** Source for [value]: private use of the proved kernel
    existence for Federer 3.3.1, p. 287. *)
Definition value (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m):=
  projT1 (cid (structure_projection_kernel_exists hmn p)).
(** Source for [laws]: the private realization satisfies the
    independent kernel specification of Federer 3.3.1, p. 287. *)
Lemma laws (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m):
  is_structure_projection_kernel p (@value R n m hmn p).
Proof. exact:projT2 (cid (structure_projection_kernel_exists hmn p)). Qed.
End StructureProjectionKernel.
