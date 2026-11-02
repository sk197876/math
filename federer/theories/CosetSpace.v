(** Public space G/S of left cosets of a subgroup S of a group G, Federer
    (1969), 2.7.1, printed p. 122: "one may take X = G/S". The space and its
    projection come from the sealed module CosetSpaceSealed.v and are used
    only through the specification is_left_coset_space of CosetSpaceUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalGroupUP CosetSpaceUP CosetSpaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coset_space]: the space G/S of left cosets of S,
    Federer 2.7.1, p. 122. Sealed definition. *)
Definition coset_space (G : topologicalType) (mul : G -> G -> G) (S : set G) : topologicalType :=
  @LeftCosetSpace.space G mul S.

(** Source for [coset_projection]: the projection g |-> g S of G onto
    G/S, Federer 2.7.1, p. 122. Sealed definition. *)
Definition coset_projection (G : topologicalType) (mul : G -> G -> G) (S : set G) :
    G -> coset_space mul S :=
  @LeftCosetSpace.projection G mul S.

(** Source for [coset_space_specification]: existence of the space
    G/S of left cosets of a subgroup S of a group G with its quotient
    topology, Federer 2.7.1, p. 122. *)
Theorem coset_space_specification (G : topologicalType) (mul : G -> G -> G) (inv : G -> G)
    (e : G) (S : set G) :
  is_group_laws mul inv e -> is_subgroup mul inv e S ->
  is_left_coset_space mul inv S (@coset_projection G mul S).
Proof. exact: LeftCosetSpace.laws. Qed.
