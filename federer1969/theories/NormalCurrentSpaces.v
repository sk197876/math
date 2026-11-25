(** Federer (1969), 4.1.7, p. 358: the
    original normal, locally normal and fixed-support
    normal-current vector spaces. Their membership
    predicates are specified independently. The
    earlier opaque subspace representation supplies
    carriers and exact linear inclusions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet CurrentSpaces CurrentSupportGeometry
  NormalCurrentsUP NormalCurrentLinear LinearSubspaceRepresentationUP LinearSubspaceRepresentationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section NormalCurrentSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation C := (fun m=>@current_space R h2 n U hU m).

(** Source for [locally_normal_current_subspace]: the
    independently defined locally normal class has
    the original vector-subspace laws, Federer
    4.1.7, p. 358. *)
Definition locally_normal_current_subspace m:subspace (C m).
Proof.
refine (@Subspace R (C m) (@is_locally_normal_current R h2 n U hU m)
  (@locally_normal_current_zero R h2 n U hU m) _ _).
- move=>T S hT hS.
  have h:=@locally_normal_current_linear R h2 n U hU m 1 T S hT hS.
  by rewrite scale1r in h.
- move=>c T hT.
  have h:=@locally_normal_current_linear R h2 n U hU m c T 0 hT
    (@locally_normal_current_zero R h2 n U hU m).
  by rewrite addr0 in h.
Defined.

(** Source for [normal_current_subspace]: the original
    normal class satisfies the vector-subspace laws,
    Federer 4.1.7, p. 358. *)
Definition normal_current_subspace m:subspace (C m).
Proof.
refine (@Subspace R (C m) (@is_normal_current R h2 n U hU m)
  (@normal_current_zero R h2 n U hU m) _ _).
- move=>T S hT hS.
  have h:=@normal_current_linear R h2 n U hU m 1 T S hT hS.
  by rewrite scale1r in h.
- move=>c T hT.
  have h:=@normal_current_linear R h2 n U hU m c T 0 hT
    (@normal_current_zero R h2 n U hU m).
  by rewrite addr0 in h.
Defined.

(** Source for [supported_normal_current_subspace]: the
    original normal currents supported in K
    form a vector subspace, supporting
    N_(m,K)(U) in Federer 4.1.7, p. 358. *)
Definition supported_normal_current_subspace m (K:smooth_compact_set hNX U):subspace (C m).
Proof.
refine (@Subspace R (C m) (@normal_currents_supported_in R h2 n U hU m K) _ _ _).
- split;first exact:normal_current_zero.
  exact:current_support_zero_subset.
- move=>T S [hT hKT] [hS hKS];split.
  + have h:=@normal_current_linear R h2 n U hU m 1 T S hT hS.
    by rewrite scale1r in h.
  + have h:=@current_support_linear_subset R h2 n m U hU K 1 T S hKT hKS.
    by rewrite scale1r in h.
- move=>c T [hT hKT];split.
  + have h:=@normal_current_linear R h2 n U hU m c T 0 hT
      (@normal_current_zero R h2 n U hU m).
    by rewrite addr0 in h.
  + have h:=@current_support_linear_subset R h2 n m U hU K c T 0 hKT
      (@current_support_zero_subset R h2 n m U hU K).
    by rewrite addr0 in h.
Defined.

(** Source for [locally_normal_current_space]: the
    original vector space N_m^loc(U),
    Federer 4.1.7, p. 358. Its
    carrier is the earlier opaque exact subspace. *)
Definition locally_normal_current_space m:lmodType R:=
  @LinearSubspaceRepresentation.space R (C m) (locally_normal_current_subspace m).

(** Source for [locally_normal_current_inclusion]: the
    original linear inclusion into D_m(U),
    supporting Federer 4.1.7, p. 358. *)
Definition locally_normal_current_inclusion m:Hom (locally_normal_current_space m) (C m):=
  @LinearSubspaceRepresentation.inclusion R (C m) (locally_normal_current_subspace m).

(** Source for [locally_normal_current_space_laws]:
    the opaque space includes injectively with
    exactly the original locally normal image,
    supporting Federer 4.1.7, p. 358. *)
Theorem locally_normal_current_space_laws m:
  is_linear_subspace_representation (locally_normal_current_subspace m) (locally_normal_current_inclusion m).
Proof. exact:LinearSubspaceRepresentation.laws. Qed.

(** Source for [normal_current_space]: the original
    vector space N_m(U), Federer 4.1.7,
    p. 358, with an opaque exact carrier. *)
Definition normal_current_space m:lmodType R:=
  @LinearSubspaceRepresentation.space R (C m) (normal_current_subspace m).

(** Source for [normal_current_inclusion]: the original
    linear inclusion of normal currents into
    D_m(U), supporting Federer 4.1.7, p. 358. *)
Definition normal_current_inclusion m:Hom (normal_current_space m) (C m):=
  @LinearSubspaceRepresentation.inclusion R (C m) (normal_current_subspace m).

(** Source for [normal_current_space_laws]: the
    opaque normal space has exactly the
    original injective inclusion and image laws,
    supporting Federer 4.1.7, p. 358. *)
Theorem normal_current_space_laws m:
  is_linear_subspace_representation (normal_current_subspace m) (normal_current_inclusion m).
Proof. exact:LinearSubspaceRepresentation.laws. Qed.

(** Source for [supported_normal_current_space]: the
    original N_(m,K)(U), Federer 4.1.7,
    p. 358, as an opaque exact subspace. *)
Definition supported_normal_current_space m (K:smooth_compact_set hNX U):lmodType R:=
  @LinearSubspaceRepresentation.space R (C m) (supported_normal_current_subspace m K).

(** Source for [supported_normal_current_inclusion]:
    the original linear inclusion of N_(m,K)(U)
    into D_m(U), supporting Federer 4.1.7,
    p. 358. *)
Definition supported_normal_current_inclusion m (K:smooth_compact_set hNX U):
    Hom (supported_normal_current_space m K) (C m):=
  @LinearSubspaceRepresentation.inclusion R (C m) (supported_normal_current_subspace m K).

(** Source for [supported_normal_current_space_laws]:
    the opaque space has precisely the original
    normal-current and compact-support image,
    supporting Federer 4.1.7, p. 358. *)
Theorem supported_normal_current_space_laws m (K:smooth_compact_set hNX U):
  is_linear_subspace_representation (supported_normal_current_subspace m K) (supported_normal_current_inclusion m K).
Proof. exact:LinearSubspaceRepresentation.laws. Qed.
End NormalCurrentSpaces.
