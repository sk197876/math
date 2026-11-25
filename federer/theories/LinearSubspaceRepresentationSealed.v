(** Federer (1969), 4.1.1, pp. 344–345: opaque carrier of a
    specified subspace, with only its linear inclusion and exact
    image laws exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient LinearSubspaceRepresentationUP
  LinearSubspaceRepresentationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type LinearSubspaceRepresentationSignature.
(** Source for [space]: the abstract prescribed subspace,
    supporting Federer 4.1.1, pp. 344–345. *)
Parameter space:forall (K:fieldType) (V:lmodType K),subspace V->lmodType K.
(** Source for [inclusion]: its linear inclusion, supporting
    the function and dual subspaces of Federer 4.1.1, pp. 344–345. *)
Parameter inclusion:forall (K:fieldType) (V:lmodType K) (S:subspace V),
  Hom (@space K V S) V.
(** Source for [laws]: exact, injective representation of the
    original subspace, supporting Federer 4.1.1, pp. 344–345. *)
Parameter laws:forall (K:fieldType) (V:lmodType K) (S:subspace V),
  is_linear_subspace_representation S (@inclusion K V S).
End LinearSubspaceRepresentationSignature.
Module LinearSubspaceRepresentation:LinearSubspaceRepresentationSignature.
(** Source for [model]: private selection of the already proved
    subspace model supporting Federer 4.1.1, pp. 344–345. *)
Definition model (K:fieldType) (V:lmodType K) (S:subspace V) :=
  cid (linear_subspace_representation_exists S).
(** Source for [space]: the hidden proved carrier supporting
    Federer 4.1.1, pp. 344–345. *)
Definition space (K:fieldType) (V:lmodType K) (S:subspace V):lmodType K :=
  projT1 (@model K V S).
(** Source for [inclusion]: the hidden model's linear inclusion,
    supporting Federer 4.1.1, pp. 344–345. *)
Definition inclusion (K:fieldType) (V:lmodType K) (S:subspace V):
    Hom (@space K V S) V := projT1 (cid (projT2 (@model K V S))).
(** Source for [laws]: the selected proved model satisfies the
    independent image specification, supporting Federer 4.1.1,
    pp. 344–345. *)
Lemma laws (K:fieldType) (V:lmodType K) (S:subspace V):
  is_linear_subspace_representation S (@inclusion K V S).
Proof. exact:(projT2 (cid (projT2 (@model K V S)))). Qed.
End LinearSubspaceRepresentation.
