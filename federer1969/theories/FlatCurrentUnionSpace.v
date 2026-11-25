(** Federer (1969), 4.1.18, p. 375: the
    codomain of the original L1 pair map
    is the compact-index union F_m(U). Its
    opaque carrier reuses the subspace already proved
    in 4.1.12, p. 368. No norm
    on the full union is asserted here. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet
  FlatCurrentsUP FlatCurrentUnion LinearSubspaceRepresentationUP
  LinearSubspaceRepresentationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section FlatCurrentUnionSpace.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation S := (@flat_current_union_subspace R h2 n m U hU).

(** Source for [flat_current_union_space]: the
    original F_m(U) codomain in Federer 4.1.18,
    p. 375, is the full union from
    4.1.12, p. 368. The carrier is
    the existing opaque representation of that precise
    subspace; no new completion or quotient is introduced. *)
Definition flat_current_union_space : lmodType R :=
  @LinearSubspaceRepresentation.space R C S.

(** Source for [flat_current_union_inclusion]: the
    original inclusion F_m(U) into D_m(U), supporting
    the pair-map representation in Federer 4.1.18,
    p. 375. The inclusion preserves actual currents. *)
Definition flat_current_union_inclusion : Hom flat_current_union_space C :=
  @LinearSubspaceRepresentation.inclusion R C S.

(** Source for [flat_current_union_space_laws]: the
    carrier has exactly the original compact-index
    union as its injectively included image, supporting
    Federer 4.1.18, p. 375, and the
    cochain domain in 4.1.19, p. 377.
    Fixed-index norms and q-image assertions are separate. *)
Theorem flat_current_union_space_laws :
  is_linear_subspace_representation S flat_current_union_inclusion.
Proof. exact: LinearSubspaceRepresentation.laws. Qed.

(** Source for [flat_current_union_inclusion_injective]:
    distinct original flat currents remain distinct
    in the codomain of q, Federer 4.1.18,
    p. 375, by the preceding exact carrier laws. *)
Lemma flat_current_union_inclusion_injective :
  injective flat_current_union_inclusion.
Proof. exact: (subspace_representation_injective flat_current_union_space_laws).
Qed.

(** Source for [flat_current_union_inclusion_member]:
    every included member has some original compact
    flat index, supporting the q codomain in
    Federer 4.1.18, p. 375. No choice
    of a compact index is exposed in the carrier. *)
Lemma flat_current_union_inclusion_member (T : flat_current_union_space) :
  @is_flat_current R h2 n m U hU (flat_current_union_inclusion T).
Proof. exact: (subspace_representation_member flat_current_union_space_laws T).
Qed.

(** Source for [flat_current_union_inclusion_full]:
    every original current in F_m(U) is represented
    by this same carrier, supporting the pair-map
    codomain in Federer 4.1.18, p. 375.
    This is a carrier assertion, not q-surjectivity. *)
Lemma flat_current_union_inclusion_full (T : C) :
  @is_flat_current R h2 n m U hU T ->
  exists S : flat_current_union_space, flat_current_union_inclusion S = T.
Proof.
exact: (@subspace_representation_full R C flat_current_union_space S
  flat_current_union_inclusion flat_current_union_space_laws T).
Qed.
End FlatCurrentUnionSpace.
