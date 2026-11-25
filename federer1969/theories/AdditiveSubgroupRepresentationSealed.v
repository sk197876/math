(** Federer (1969), 4.1.22, p. 379: opaque carriers
    of the prescribed integral polyhedral subgroups. Expose
    only the additive inclusion and independently proved
    exact-image laws; hide the chosen subtype model. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import TopologicalGroupUP AdditiveSubgroupRepresentationUP
  AdditiveSubgroupRepresentationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type AdditiveSubgroupRepresentationSignature.
(** Source: the abstract original abelian subgroup carrier,
    supporting Federer 4.1.22, p. 379. *)
Parameter space:forall (V:zmodType) (S:set V),
  is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S->zmodType.
(** Source: its original additive current inclusion,
    supporting Federer 4.1.22, p. 379. *)
Parameter inclusion:forall (V:zmodType) (S:set V)
  (hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S),
  {additive @space V S hS->V}.
(** Source: the original injective exact-image laws,
    supporting Federer 4.1.22, p. 379. *)
Parameter laws:forall (V:zmodType) (S:set V)
  (hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S),
  is_additive_subgroup_representation S (@inclusion V S hS).
End AdditiveSubgroupRepresentationSignature.

Module AdditiveSubgroupRepresentation:AdditiveSubgroupRepresentationSignature.
(** Source: hide selection of the proved carrier witness,
    supporting Federer 4.1.22, p. 379. *)
Definition model (V:zmodType) (S:set V)
    (hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S):=
  cid (@additive_subgroup_representation_exists V S hS).
(** Source: the opaque abelian carrier,
    supporting Federer 4.1.22, p. 379. *)
Definition space (V:zmodType) (S:set V)
    (hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S):zmodType:=
  projT1 (@model V S hS).
(** Source: its opaque additive inclusion,
    supporting Federer 4.1.22, p. 379. *)
Definition inclusion (V:zmodType) (S:set V)
    (hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S):
    {additive @space V S hS->V}:=
  projT1 (cid (projT2 (@model V S hS))).
(** Source: the hidden model satisfies the independent original
    image specification, supporting Federer 4.1.22, p. 379. *)
Lemma laws (V:zmodType) (S:set V)
    (hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S):
  is_additive_subgroup_representation S (@inclusion V S hS).
Proof. exact:(projT2 (cid (projT2 (@model V S hS)))). Qed.
End AdditiveSubgroupRepresentation.
