(** Federer (1969), 4.1.1, pp. 344–345: E'(U,Y) and
    D'(U,Y) are the vector spaces of continuous real linear
    functionals. Their definition uses actual continuity, without
    requiring the source topology to be a vector topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP OpenFamilyTopologyUP
  OpenVectorTopologyUP OpenFamilyContinuousOperations DirectedSeminormVectorTopology
  NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [continuous_real_dual_subspace]: direct definition
    of the continuous real linear dual in Federer 4.1.1,
    pp. 344–345. Closure under vector operations is proved from
    continuity of the scalar target operations. *)
Definition continuous_real_dual_subspace (R:realType) (E:lmodType R)
    (O:set (set E)) (hO:is_open_family_topology O):subspace (Hom E R^o).
Proof.
pose hN:=@scalar_absolute_value_norm R.
pose Q:=norm_open_family hN.
pose hQ:=
  seminorm_family_vector_topology (norm_single_seminorm_directed hN)
    (norm_open_family_seminorm_laws hN).
refine (@Subspace R (Hom E R^o) (fun L=>open_family_continuous O Q L) _ _ _).
- change (open_family_continuous O Q (fun _=>0)).
  exact:open_family_constant_continuous hO.
- move=>L M hL hM; change (open_family_continuous O Q (fun x=>L x+M x)).
  exact:(@open_family_continuous_add R E R^o O Q hO hQ L M hL hM).
- move=>c L hL; change (open_family_continuous O Q (fun x=>c*:L x)).
  exact:(@open_family_continuous_scale R E R^o O Q hO hQ L c hL).
Defined.
