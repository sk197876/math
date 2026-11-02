(** Federer (1969), 2.7.10, printed p. 127: "To each x in X and each left
    Haar integral mu of the isotropy group G^x corresponds a linear
    epimorphism mu^x: K(G) -> K(X) with the following properties: (1)
    mu^x(u)(g x) = mu_s[u(g s)] whenever u in K(G), g in G." The map mu^x is
    specified here by the two conditions which determine it: it maps K(G)
    into K(X), and it satisfies (1). Since every point of X has the form g x
    = A(g,x), condition (1) determines mu^x(u) for each u in K(G); the
    uniqueness, the linearity, the surjectivity and the properties (2)–(6)
    are derived from this specification in CosetIntegralLaws.v, and its
    existence is proved in CosetIntegralExistence.v. The isotropy group G^x
    is the type set_type (isotropy_subgroup A x) with the relative topology
    (IsotropyGroupTopology.v); mu_s[u(g s)] is mu applied to the function s
    |-> u(g s) on G^x, so that mu^x(u)(g x) is the integral of u over the
    coset g G^x. Federer gives the map no name; it is called a coset
    integral here. The values of mu^x outside K(G) are not specified. *)
From mathcomp Require Import all_boot boolp classical_sets functions reals topology.
From Federer Require Import CompactSupportFunctionUP HomogeneousSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_coset_integral]: the map mu^x: K(G) -> K(X) of
    Federer 2.7.10, p. 127, with "(1) mu^x(u)(g x) = mu_s[u(g s)]
    whenever u in K(G), g in G". Definition by these two conditions,
    for a function mu on the real functions on G^x; the hypotheses that
    mu is a left Haar integral of G^x and that X is a homogeneous space
    belong to the results. *)
Record is_coset_integral (R : realType) (G X : topologicalType) (mul : G -> G -> G)
    (A : G -> X -> X) (x : X) (mu : (isotropy_subgroup A x -> R) -> R)
    (M : (G -> R) -> X -> R) : Prop := {
  (** Source for [coset_integral_compact]: "mu^x: K(G) -> K(X)",
      Federer 2.7.10, p. 127. *)
  coset_integral_compact : forall u, @compactly_supported_continuous_functions R G u ->
    @compactly_supported_continuous_functions R X (M u);
  (** Source for [coset_integral_value]: "(1) mu^x(u)(g x) =
      mu_s[u(g s)] whenever u in K(G), g in G", Federer 2.7.10, p. 127,
      with g x = A(g,x) (2.7.1, p. 122). *)
  coset_integral_value : forall u g, @compactly_supported_continuous_functions R G u ->
    M u (A g x) = mu (fun s => u (mul g (set_val s)))
}.

Arguments is_coset_integral [R G X] mul A x mu M.
