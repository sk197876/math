(** Opaque implementation of the space G/S of left cosets of a subgroup S of
    a group G, Federer (1969), 2.7.1, printed p. 122. The signature exposes
    only the space, the projection and its specification is_left_coset_space
    of CosetSpaceUP.v; downstream results use the specification, never the
    construction of CosetSpaceConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalGroupUP CosetSpaceUP CosetSpaceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type LeftCosetSpaceSignature.
  (** Source for [space]: the space G/S of Federer 2.7.1, p. 122,
      exposed through its specification. *)
  Parameter space : forall (G : topologicalType), (G -> G -> G) -> set G -> topologicalType.
  (** Source for [projection]: the projection g |-> g S of Federer
      2.7.1, p. 122, exposed through its specification. *)
  Parameter projection : forall (G : topologicalType) (mul : G -> G -> G) (S : set G),
    G -> space mul S.
  (** Source for [laws]: the specification of G/S for a subgroup S
      of a group G, Federer 2.7.1, p. 122. *)
  Parameter laws : forall (G : topologicalType) (mul : G -> G -> G) (inv : G -> G) (e : G)
    (S : set G), is_group_laws mul inv e -> is_subgroup mul inv e S ->
    is_left_coset_space mul inv S (@projection G mul S).
End LeftCosetSpaceSignature.

Module LeftCosetSpace : LeftCosetSpaceSignature.
(** Source for [space]: witness of the space G/S of Federer 2.7.1,
    p. 122. *)
Definition space (G : topologicalType) (mul : G -> G -> G) (S : set G) : topologicalType :=
  @coset_space_witness G mul S.
(** Source for [projection]: witness of the projection of Federer
    2.7.1, p. 122. *)
Definition projection (G : topologicalType) (mul : G -> G -> G) (S : set G) : G -> space mul S :=
  @coset_projection_witness G mul S.
(** Source for [laws]: proved specification of the witness of G/S,
    Federer 2.7.1, p. 122. No new global assumption is introduced. *)
Lemma laws (G : topologicalType) (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) :
  is_group_laws mul inv e -> is_subgroup mul inv e S ->
  is_left_coset_space mul inv S (@projection G mul S).
Proof. exact: coset_space_witness_laws. Qed.
End LeftCosetSpace.
