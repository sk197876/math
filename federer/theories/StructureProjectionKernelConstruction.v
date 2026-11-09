(** Existence and uniqueness of the actual kernel plane in
    Federer (1969), 3.3.1, p. 287. Reuse the previously proved
    kernel-dimension theorem of 2.7.16(7), p. 140. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanProjectionSpace OrthogonalProjectionFibres StructureProjectionKernelUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_projection_kernel_exists]: the target
    G(n,n-m) in Federer 3.3.1, p. 287. The actual kernel has the
    required dimension by 2.7.16(7), p. 140; double subtraction
    merely identifies the earlier projection's codomain with R^m.
    Both zero and full projection dimensions are retained. *)
Theorem structure_projection_kernel_exists (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m):
  exists K,is_structure_projection_kernel p K.
Proof.
have h:=@projection_kernel_exists R n (n-m) (leq_subr m n).
have hdim:(n-(n-m)=m)%N by rewrite subKn.
rewrite hdim in h.
exact:h p.
Qed.

(** Source for [structure_projection_kernel_unique]: uniqueness
    of the plane ker p in Federer 3.3.1, p. 287. Extensionality
    of the original Grassmann space suffices. *)
Theorem structure_projection_kernel_unique (R:realType) n m
    (p:euclidean_projection_space R n m) K L:
  is_structure_projection_kernel p K ->is_structure_projection_kernel p L ->K=L.
Proof.
move=>hK hL; apply:grassmann_ext=>x; split.
- move/hK=>hx; exact/hL.
- move/hL=>hx; exact/hK.
Qed.
