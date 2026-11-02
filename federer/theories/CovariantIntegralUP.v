(** Federer (1969), 2.7.1, printed p. 122: "A Daniell integral mu on K(X) is
    called a chi covariant integral if and only if chi: G -> R and mu(u o
    A_g) = chi(g) mu(u) whenever u in K(X), g in G. ... In particular, if
    chi(g) = 1 for all g in G, one calls mu an invariant integral (with
    respect to the action A of G on X). The K(X) regular measure associated
    with a monotone chi covariant (invariant) integral is termed a chi
    covariant (invariant) measure." Here K(X) is
    compactly_supported_continuous_functions of 2.5.13, a Daniell integral
    is is_daniell_integral of 2.5.5, and the K(X) regular measure associated
    with a monotone Daniell integral is the K(X) regular measure
    representing it (2.5.2-2.5.3), which is unique by
    monotone_daniell_regular_representation. The covariance identity is
    stated separately for an arbitrary class L of functions, so that it
    applies also to the variation integral on K(X)+ of 2.5.6. Federer's
    abbreviations u o A_g = u_g and A(g,x) = g x are notation only and are
    not introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP
  CompactSupportFunctionUP FunctionLatticeRegularityUP RealIntegralFunctionalUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_covariant_on]: the identity "mu(u o A_g) =
    chi(g) mu(u) whenever u in K(X), g in G" of Federer 2.7.1, p. 122,
    for the functions u of a class L. Definition. *)
Definition is_covariant_on (R : realType) (G X : Type) (L : set (X -> R)) (A : G -> X -> X)
    (chi : G -> R) (mu : (X -> R) -> R) : Prop :=
  forall u g, L u -> mu (u \o A g) = chi g * mu u.

(** Source for [is_covariant_integral]: "A Daniell integral mu on K(X)
    is called a chi covariant integral if and only if chi: G -> R and
    mu(u o A_g) = chi(g) mu(u) whenever u in K(X), g in G", Federer
    2.7.1, p. 122. Direct definition. *)
Record is_covariant_integral (R : realType) (G : Type) (X : topologicalType) (A : G -> X -> X)
    (chi : G -> R) (mu : (X -> R) -> R) : Prop := {
  (** Source for [covariant_integral_daniell]: mu is a Daniell
      integral on K(X), Federer 2.7.1, p. 122. *)
  covariant_integral_daniell : is_daniell_integral (@compactly_supported_continuous_functions R X) mu;
  (** Source for [covariant_integral_law]: mu(u o A_g) = chi(g) mu(u)
      whenever u in K(X), g in G, Federer 2.7.1, p. 122. *)
  covariant_integral_law : is_covariant_on (@compactly_supported_continuous_functions R X) A chi mu
}.

(** Source for [is_invariant_integral]: "if chi(g) = 1 for all g in
    G, one calls mu an invariant integral (with respect to the action A
    of G on X)", Federer 2.7.1, p. 122. Direct definition. *)
Definition is_invariant_integral (R : realType) (G : Type) (X : topologicalType) (A : G -> X -> X)
    (mu : (X -> R) -> R) : Prop :=
  is_covariant_integral A (fun _ => 1) mu.

(** Source for [is_covariant_measure]: "The K(X) regular measure
    associated with a monotone chi covariant ... integral is termed a
    chi covariant ... measure", Federer 2.7.1, p. 122. Definition:
    phi is the K(X) regular measure representing some monotone Daniell
    integral on K(X) which satisfies the chi covariance identity. *)
Definition is_covariant_measure (R : realType) (G : Type) (X : topologicalType) (A : G -> X -> X)
    (chi : G -> R) (phi : set X -> \bar R) : Prop :=
  exists mu : (X -> R) -> R,
    [/\ is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) mu,
      is_covariant_on (@compactly_supported_continuous_functions R X) A chi mu,
      is_measure phi,
      is_real_integral_functional phi (@compactly_supported_continuous_functions R X) mu &
      is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi].

(** Source for [is_invariant_measure]: "The K(X) regular measure
    associated with a monotone ... invariant integral is termed a ...
    invariant measure", Federer 2.7.1, p. 122. Direct definition. *)
Definition is_invariant_measure (R : realType) (G : Type) (X : topologicalType) (A : G -> X -> X)
    (phi : set X -> \bar R) : Prop :=
  is_covariant_measure A (fun _ => 1) phi.
