(** Federer (1969), 2.7.1, printed p. 122: the spaces G/G^x and G/S of left
    cosets, in "A^x induces a homeomorphism G/G^x ~ X, which maps each coset
    g G^x onto A(g,x)" and "one may take X = G/S and A(g, hS) = g h S".
    Federer uses the space of left cosets with its quotient topology without
    further description. It is specified here by the projection pi: G ->
    G/S: pi maps G onto G/S, pi g = pi h holds if and only if g^{-1} h
    belongs to S (that is, g S = h S, see CosetSpaceLaws.v), and a subset of
    G/S is open if and only if its inverse image under pi is open in G. The
    universal property for maps constant on cosets is derived from this
    specification in CosetSpaceLaws.v; existence is proved in
    CosetSpaceConstruction.v and sealed in CosetSpaceSealed.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_left_coset_space]: the space G/S of left cosets of
    a subgroup S of G with the quotient topology, Federer 2.7.1, p. 122.
    Definition by the laws of the projection pi: G -> G/S, g |-> g S.
    The points of G/S are the cosets: pi g = pi h exactly when
    g^{-1} h is in S. *)
Record is_left_coset_space (G Q : topologicalType) (mul : G -> G -> G) (inv : G -> G)
    (S : set G) (pi : G -> Q) : Prop := {
  (** Source for [coset_projection_onto]: every point of G/S is a
      coset g S, Federer 2.7.1, p. 122. *)
  coset_projection_onto : forall q, exists g, pi g = q;
  (** Source for [coset_projection_eq]: g S = h S if and only if
      g^{-1} h belongs to S, for the cosets of Federer 2.7.1,
      p. 122. *)
  coset_projection_eq : forall g h, pi g = pi h <-> S (mul (inv g) h);
  (** Source for [coset_space_open]: the quotient topology of G/S,
      Federer 2.7.1, p. 122. *)
  coset_space_open : forall U : set Q, open U <-> open (pi @^-1` U)
}.
