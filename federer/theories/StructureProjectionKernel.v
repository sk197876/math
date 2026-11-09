(** Public kernel map of Federer (1969), 3.3.1, p. 287.
    Its values are the original Grassmann planes, and its proved
    opaque laws retain the original orthogonal projections. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanProjectionSpace StructureProjectionKernelUP StructureProjectionKernelSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [structure_projection_kernel]: p maps to ker p,
    the final sentence of Federer 3.3.1, p. 287. *)
Definition structure_projection_kernel (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m):=
  @StructureProjectionKernel.value R n m hmn p.

(** Source for [structure_projection_kernelE]: membership in
    the actual ker p of Federer 3.3.1, p. 287, is exactly
    annihilation by the original p. *)
Lemma structure_projection_kernelE (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m) x:
  grassmann_val (structure_projection_kernel hmn p) x <->
    euclidean_projection_linear p x=0.
Proof. exact:StructureProjectionKernel.laws. Qed.
