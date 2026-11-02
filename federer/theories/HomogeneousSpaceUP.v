(** Federer (1969), 2.7.1, printed p. 121: "we assume that X is a
    homogeneous space of G through the transitive left action A: G x X -> X;
    this means that A is continuous, that A(gh,x) = A[g,A(h,x)] for g in G,
    h in G, x in X, and that for each x in X the map A^x: G -> X, A^x(g) =
    A(g,x) whenever g in G, is open with im A^x = X." The action is written
    in curried form A g x, so that A g is Federer's A_g; the continuity of A
    refers to the product topology of G x X. As printed, A(e,x) = x is not
    assumed; it is derived in HomogeneousSpaceLaws.v. The specification
    records only the conditions of the definition; that G is a locally
    compact Hausdorff topological group and X a locally compact Hausdorff
    space are separate hypotheses of the results. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [orbit_map]: the map A^x: G -> X, A^x(g) = A(g,x)
    whenever g in G, of Federer 2.7.1, p. 121. Direct definition. *)
Definition orbit_map (G X : Type) (A : G -> X -> X) (x : X) : G -> X := fun g => A g x.

(** Source for [isotropy_subgroup]: "the isotropy subgroup
    G^x = G cap {g: A(g,x) = x}", Federer 2.7.1, p. 121. Direct
    definition; that it is a closed subgroup is proved in
    HomogeneousSpaceLaws.v. *)
Definition isotropy_subgroup (G X : Type) (A : G -> X -> X) (x : X) : set G := [set g | A g x = x].

(** Source for [is_homogeneous_space]: Federer 2.7.1, p. 121,
    definition of "X is a homogeneous space of G through the
    transitive left action A". Direct formalisation of the four
    printed conditions. *)
Record is_homogeneous_space (G X : topologicalType) (mul : G -> G -> G) (A : G -> X -> X) : Prop := {
  (** Source for [homogeneous_action_continuous]: "A is continuous",
      Federer 2.7.1, p. 121, for the product topology of G x X. *)
  homogeneous_action_continuous : continuous (fun p : G * X => A p.1 p.2);
  (** Source for [homogeneous_action_compatible]: "A(gh,x) =
      A[g,A(h,x)] for g in G, h in G, x in X", Federer 2.7.1, p. 121. *)
  homogeneous_action_compatible : forall g h x, A (mul g h) x = A g (A h x);
  (** Source for [homogeneous_orbit_open]: "for each x in X the map
      A^x ... is open", Federer 2.7.1, p. 121. *)
  homogeneous_orbit_open : forall x, is_open_map (orbit_map A x);
  (** Source for [homogeneous_orbit_onto]: "im A^x = X", Federer 2.7.1,
      p. 121. *)
  homogeneous_orbit_onto : forall x, orbit_map A x @` setT = setT
}.
