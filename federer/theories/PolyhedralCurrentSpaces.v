(** Federer (1969), 4.1.22, p. 379: opaque abelian
    group and real vector-space carriers for the original
    integral and real polyhedral classes. All four predicates
    are independently defined on actual currents. Reuse the
    exact additive and linear representation interfaces, exposing
    only injective inclusions and their original full images. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet AdditiveSubgroupRepresentationUP
  AdditiveSubgroupRepresentationSealed LinearSubspaceRepresentationUP
  LinearSubspaceRepresentationSealed PolyhedralCurrentAlgebra PolyhedralCurrentUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section PolyhedralCurrentSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation Index := (smooth_compact_set hNX U).
Local Notation Integral K := (@integral_polyhedral_current_class R h2 n m U hU K).
Local Notation hIntegral K := (@integral_polyhedral_current_subgroup R h2 n m U hU K).
Local Notation Real K := (@polyhedral_current_subspace R h2 n m U hU K).
Local Notation IntegralUnion := (@is_integral_polyhedral_current R h2 n m U hU).
Local Notation hIntegralUnion := (@integral_polyhedral_union_subgroup R h2 n m U hU).
Local Notation RealUnion := (@polyhedral_current_union_subspace R h2 n m U hU).

(** Source for [integral_polyhedral_current_space]: the opaque
    abelian group P-script_(m,K)(U), Federer 4.1.22, p. 379. *)
Definition integral_polyhedral_current_space (K:Index):zmodType:=
  @AdditiveSubgroupRepresentation.space C (Integral K) (hIntegral K).

(** Source for [integral_polyhedral_current_inclusion]: the
    original additive inclusion into D_m(U),
    Federer 4.1.22, p. 379. *)
Definition integral_polyhedral_current_inclusion (K:Index):
    {additive integral_polyhedral_current_space K->C}:=
  @AdditiveSubgroupRepresentation.inclusion C
    (Integral K) (hIntegral K).

(** Source for [integral_polyhedral_current_space_laws]: the
    fixed-K abelian carrier has exactly the original subgroup
    as its injective additive image, Federer 4.1.22, p. 379. *)
Theorem integral_polyhedral_current_space_laws (K:Index):
  is_additive_subgroup_representation (Integral K)
    (integral_polyhedral_current_inclusion K).
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

(** Source for [polyhedral_current_space]: the opaque real
    vector space P_(m,K)(U), Federer 4.1.22, p. 379. *)
Definition polyhedral_current_space (K:Index):lmodType R:=
  @LinearSubspaceRepresentation.space R C (Real K).

(** Source for [polyhedral_current_inclusion]: the original
    real-linear inclusion into D_m(U),
    Federer 4.1.22, p. 379. *)
Definition polyhedral_current_inclusion (K:Index):Hom (polyhedral_current_space K) C:=
  @LinearSubspaceRepresentation.inclusion R C (Real K).

(** Source for [polyhedral_current_space_laws]: the fixed-K
    vector carrier has exactly the original real span as
    its injective linear image, Federer 4.1.22, p. 379. *)
Theorem polyhedral_current_space_laws (K:Index):
  is_linear_subspace_representation (Real K) (polyhedral_current_inclusion K).
Proof. exact:LinearSubspaceRepresentation.laws. Qed.

(** Source for [integral_polyhedral_current_union_space]: the
    opaque abelian group of all original integral polyhedral
    m-chains in U, Federer 4.1.22, p. 379. Its image
    is the literal union over every compact index. *)
Definition integral_polyhedral_current_union_space:zmodType:=
  @AdditiveSubgroupRepresentation.space C IntegralUnion hIntegralUnion.

(** Source for [integral_polyhedral_current_union_inclusion]:
    the original additive inclusion of integral polyhedral
    chains into D_m(U), Federer 4.1.22, p. 379. *)
Definition integral_polyhedral_current_union_inclusion:
    {additive integral_polyhedral_current_union_space->C}:=
  @AdditiveSubgroupRepresentation.inclusion C
    IntegralUnion hIntegralUnion.

(** Source for [integral_polyhedral_current_union_space_laws]:
    the original integral union is an abelian group with
    exactly its prescribed current image, Federer
    4.1.22, p. 379. *)
Theorem integral_polyhedral_current_union_space_laws:
  is_additive_subgroup_representation IntegralUnion
    integral_polyhedral_current_union_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

(** Source for [polyhedral_current_union_space]: the opaque
    real vector space of all original polyhedral m-chains
    in U, Federer 4.1.22, p. 379. *)
Definition polyhedral_current_union_space:lmodType R:=
  @LinearSubspaceRepresentation.space R C RealUnion.

(** Source for [polyhedral_current_union_inclusion]: the
    original real-linear inclusion of the full polyhedral
    space into D_m(U), Federer 4.1.22, p. 379. *)
Definition polyhedral_current_union_inclusion:Hom polyhedral_current_union_space C:=
  @LinearSubspaceRepresentation.inclusion R C RealUnion.

(** Source for [polyhedral_current_union_space_laws]: the
    opaque real carrier has precisely the original compact
    union as its injective linear image,
    Federer 4.1.22, p. 379. *)
Theorem polyhedral_current_union_space_laws:
  is_linear_subspace_representation RealUnion polyhedral_current_union_inclusion.
Proof. exact:LinearSubspaceRepresentation.laws. Qed.
End PolyhedralCurrentSpaces.
