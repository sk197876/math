(** Federer (1969), 4.1.1, pp. 344–345: opaque corestriction
    of a supplied linear map to a specified subspace. Consumers
    use only the equality after inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient LinearSubspaceRepresentationUP LinearSubspaceLiftExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type LinearSubspaceLiftSignature.
(** Source for [map]: corestriction preserves the given linear
    map, supporting the subspaces of Federer 4.1.1, pp. 344–345. *)
Parameter map:forall (K:fieldType) (E W V:lmodType K)
    (S:subspace V) (inc:Hom W V),
  is_linear_subspace_representation S inc ->
  forall L:Hom E V,(forall x,S (L x))->Hom E W.
(** Source for [evaluation]: the original values of the
    corestricted map, supporting Federer 4.1.1, pp. 344–345. *)
Parameter evaluation:forall (K:fieldType) (E W V:lmodType K)
    (S:subspace V) (inc:Hom W V) (hW:is_linear_subspace_representation S inc)
    (L:Hom E V) (hL:forall x,S (L x)) x,
  inc (@map K E W V S inc hW L hL x)=L x.
End LinearSubspaceLiftSignature.
Module LinearSubspaceLift:LinearSubspaceLiftSignature.
(** Source for [map]: select the proved corestriction witness,
    supporting Federer 4.1.1, pp. 344–345. *)
Definition map (K:fieldType) (E W V:lmodType K)
    (S:subspace V) (inc:Hom W V) (hW:is_linear_subspace_representation S inc)
    (L:Hom E V) (hL:forall x,S (L x)):Hom E W:=
  projT1 (cid (linear_subspace_lift_exists hW hL)).
(** Source for [evaluation]: the selected witness has its
    independent value law, supporting Federer 4.1.1, pp. 344–345. *)
Lemma evaluation (K:fieldType) (E W V:lmodType K)
    (S:subspace V) (inc:Hom W V) (hW:is_linear_subspace_representation S inc)
    (L:Hom E V) (hL:forall x,S (L x)) x:
  inc (@map K E W V S inc hW L hL x)=L x.
Proof. exact:(projT2 (cid (linear_subspace_lift_exists hW hL)) x). Qed.
End LinearSubspaceLift.
