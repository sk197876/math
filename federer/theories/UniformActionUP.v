(** Federer (1969), 2.7.3, printed p. 123: "We shall say that G acts
    uniformly on X if and only if the topology of X is induced by some
    uniformity with a G invariant basis B; by saying that B is G invariant
    we mean that, whenever beta in B and g in G, (x,y) in beta if and only
    if (gx,gy) in beta. One easily verifies that G acts uniformly on X if
    and only if for each neighborhood V of a point x in X there exists a
    neighborhood W of x such that g in G, W cap A_g(W) <> empty implies
    A_g(W) subset V; when this condition holds one may take as B the family
    of the sets U_{g in G} A_g(V) x A_g(V) corresponding to all nonempty
    open subsets V of X." MathComp's uniformType is a structure carried by a
    type, so that "some uniformity" inducing the given topology of X cannot
    be quantified over directly. A uniformity on X is therefore specified by
    a predicate on a family E of subsets of X x X, whose fields are exactly
    the entourage laws of MathComp's factory Nbhs_isUniform: E is a filter,
    its members contain the diagonal, it is closed under inversion of
    relations, and each member contains D o D for some member D. It induces
    the topology of X when the neighbourhoods of each x are the sets
    containing a section {y : (x,y) in D} with D in E, as in MathComp's
    nbhs_. A basis B of E is a subfamily such that each member of E contains
    a member of B. The lemma uniform_type_uniformity shows that the
    entourages of every MathComp uniform space satisfy the predicate. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope relation_scope.

(** Source for [is_uniformity]: "some uniformity", Federer 2.7.3,
    p. 123. Definition of the uniformities on a set X by the entourage
    laws, which are the fields of MathComp's factory Nbhs_isUniform
    apart from its condition on neighbourhoods. *)
Record is_uniformity (X : Type) (E : set_system (X * X)) : Prop := {
  (** Source for [uniformity_filter]: the entourages form a filter,
      Federer 2.7.3, p. 123. *)
  uniformity_filter : Filter E;
  (** Source for [uniformity_diagonal]: each entourage contains the
      diagonal, Federer 2.7.3, p. 123. *)
  uniformity_diagonal : forall D, E D -> diagonal `<=` D;
  (** Source for [uniformity_inverse]: the inverse relation of an
      entourage is an entourage, Federer 2.7.3, p. 123. *)
  uniformity_inverse : forall D, E D -> E D^-1;
  (** Source for [uniformity_split]: each entourage contains the
      composition of some entourage with itself, Federer 2.7.3,
      p. 123. *)
  uniformity_split : forall D, E D -> exists2 D', E D' & D' \; D' `<=` D
}.

(** Source for [uniformity_induces_topology]: "the topology of X is
    induced by some uniformity", Federer 2.7.3, p. 123. Definition: the
    neighbourhoods of x in X are the sets containing a section
    {y : (x,y) in D} with D in E, as in the condition nbhsE of
    MathComp's factory Nbhs_isUniform. *)
Definition uniformity_induces_topology (X : topologicalType) (E : set_system (X * X)) : Prop :=
  forall x : X, nbhs x = nbhs_ E x.

(** Source for [is_uniformity_basis]: "a ... basis B" of a
    uniformity, Federer 2.7.3, p. 123. Definition: B is a subfamily of
    E, and every member of E contains a member of B. *)
Definition is_uniformity_basis (X : Type) (E B : set_system (X * X)) : Prop :=
  B `<=` E /\ forall D, E D -> exists2 beta, B beta & beta `<=` D.

(** Source for [is_invariant_entourage_family]: "by saying that B is
    G invariant we mean that, whenever beta in B and g in G, (x,y) in
    beta if and only if (gx,gy) in beta", Federer 2.7.3, p. 123, with
    gx = A(g,x) as in 2.7.1, p. 122. Direct definition. *)
Definition is_invariant_entourage_family (G X : Type) (A : G -> X -> X)
    (B : set_system (X * X)) : Prop :=
  forall beta g x y, B beta -> beta (x, y) <-> beta (A g x, A g y).

(** Source for [acts_uniformly]: "We shall say that G acts uniformly
    on X if and only if the topology of X is induced by some uniformity
    with a G invariant basis B", Federer 2.7.3, p. 123. Direct
    definition. *)
Definition acts_uniformly (G : Type) (X : topologicalType) (A : G -> X -> X) : Prop :=
  exists E B : set_system (X * X),
    [/\ is_uniformity E, uniformity_induces_topology E, is_uniformity_basis E B &
      is_invariant_entourage_family A B].

(** Source for [uniform_action_condition]: "for each neighborhood V
    of a point x in X there exists a neighborhood W of x such that g in
    G, W cap A_g(W) <> empty implies A_g(W) subset V", Federer 2.7.3,
    p. 123. Direct definition. *)
Definition uniform_action_condition (G : Type) (X : topologicalType) (A : G -> X -> X) : Prop :=
  forall (x : X) (V : set X), nbhs x V ->
    exists2 W, nbhs x W & forall g, W `&` A g @` W !=set0 -> A g @` W `<=` V.

(** Source for [orbit_entourage]: "the sets U_{g in G} A_g(V) x A_g(V)",
    Federer 2.7.3, p. 123. Direct definition for a subset V of X. *)
Definition orbit_entourage (G X : Type) (A : G -> X -> X) (V : set X) : set (X * X) :=
  \bigcup_(g in [set: G]) (A g @` V `*` A g @` V).

(** Source for [orbit_entourage_family]: "the family of the sets
    U_{g in G} A_g(V) x A_g(V) corresponding to all nonempty open
    subsets V of X", Federer 2.7.3, p. 123. Direct definition. *)
Definition orbit_entourage_family (G : Type) (X : topologicalType) (A : G -> X -> X) :
    set_system (X * X) :=
  [set orbit_entourage A V | V in [set V : set X | open V /\ V !=set0]].

(** Source for [uniform_type_uniformity]: supporting the choice of
    the predicates for "uniformity" in Federer 2.7.3, p. 123: the
    entourages of a MathComp uniform space form a uniformity inducing
    its topology. *)
Lemma uniform_type_uniformity (M : uniformType) :
  is_uniformity (@entourage M) /\ uniformity_induces_topology (@entourage M).
Proof.
split; last by move=> x; rewrite nbhs_entourageE.
constructor.
- exact: entourage_filter.
- by move=> D hD [x y] /diagonalP <-; exact: entourage_refl.
- exact: entourage_inv.
- exact: entourage_split_ex.
Qed.
