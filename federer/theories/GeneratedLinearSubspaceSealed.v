(** Federer (1969), 4.1.22, p. 379: the algebraic
    real span is opaque and exposes only its independently
    specified least-subspace laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import ModuleQuotient GeneratedLinearSubspaceUP
  GeneratedLinearSubspaceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type GeneratedLinearSubspaceSignature.
(** Source: the real span of the original integral subgroup,
    Federer 4.1.22, p. 379. *)
Parameter value:forall (K:fieldType) (V:lmodType K),set V->subspace V.
(** Source: the independent algebraic least-subspace laws,
    Federer 4.1.22, p. 379. *)
Parameter laws:forall (K:fieldType) (V:lmodType K) (D:set V),
  is_generated_linear_subspace D (@value K V D).
End GeneratedLinearSubspaceSignature.

Module GeneratedLinearSubspace:GeneratedLinearSubspaceSignature.
(** Source: hide the proved span witness, supporting
    Federer 4.1.22, p. 379. *)
Definition value (K:fieldType) (V:lmodType K) (D:set V):subspace V:=
  projT1 (cid (@generated_linear_subspace_exists K V D)).
(** Source: the opaque span satisfies the original independent
    specification, supporting Federer 4.1.22, p. 379. *)
Lemma laws (K:fieldType) (V:lmodType K) (D:set V):
  is_generated_linear_subspace D (@value K V D).
Proof. exact:(projT2 (cid (@generated_linear_subspace_exists K V D))). Qed.
End GeneratedLinearSubspace.
