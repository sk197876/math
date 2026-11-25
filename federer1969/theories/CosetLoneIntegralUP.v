(** Federer (1969), 2.7.13, printed p. 130: "Suppose gamma is the K(X)
    regular measure associated with a monotone Daniell integral nu, x in X,
    beta is the K(G^x) regular measure associated with a left Haar integral
    mu of G^x, and alpha is the K(G) regular measure associated with the
    monotone Daniell integral nu o mu^x (see 2.7.10). Then there exists a
    linear epimorphism beta^x: L_1(alpha) -> L_1(gamma) such that, for each
    alpha summable function u, beta^x(u)(g x) = integral u(g s) d beta s
    whenever g in G, integral beta^x(u) d gamma = integral u d alpha." The
    map beta^x is specified here by these two laws, for maps B sending each
    real function u on G to a real function B u on X. The fibre formula is
    required for gamma almost all points y of X and for every g in G with g
    x = y; this is the reading given by the proof, where beta^x(u) is the
    function T(u) with domain E(u) = {g x: integral u(g s) d beta s in R}
    and gamma[X ~ E(u)] = 0. The functions are total and real valued, as in
    the proof ("With each u: G -> R we associate T(u)"); L_1 is the
    total-domain space of the erratum, p. 2 (book p. 98 line 10), and a
    function of L_1(gamma) is determined only up to gamma almost equality.
    The values B u for functions u which are not alpha summable are not
    specified. The point g x is A(g,x) (2.7.1, p. 121), G^x is the type
    set_type (isotropy_subgroup A x) (IsotropyGroupTopology.v), and u(g s)
    is u(mul g (set_val s)). Existence, linearity and surjectivity are
    proved in CosetLoneIntegralExistence.v and CosetLoneIntegralOnto.v. The
    local erratum has no entry for pp. 130–131. *)
From mathcomp Require Import all_boot boolp classical_sets functions reals constructive_ereal topology.
From Federer Require Import MeasureAlmostUP MeasureIntegralUP SummableRealFunctionUP HomogeneousSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coset_fibre_integral]: "beta^x(u)(g x) = integral
    u(g s) d beta s whenever g in G", Federer 2.7.13, p. 130, at one
    point y = g x of X with value r: for every g in G with g x = y the
    function s |-> u(g s) on G^x has the beta integral r. Definition;
    the proof writes "E(u) = {g x: integral u(g s) d beta s in R}" and
    "T(u)(g x) = integral u(g s) d beta s whenever g x in E(u)". *)
Definition coset_fibre_integral (R : realType) (G X : topologicalType) (mul : G -> G -> G)
    (A : G -> X -> X) (x : X) (beta : set (isotropy_subgroup A x) -> \bar R) (u : G -> R)
    (y : X) (r : R) : Prop :=
  forall g, A g x = y ->
    is_measure_integral beta (real_total_integrand (fun s : isotropy_subgroup A x => u (mul g (set_val s))))
      r%:E.

Arguments coset_fibre_integral [R G X] mul A x beta u y r.

(** Source for [is_coset_lone_integral]: the map
    beta^x: L_1(alpha) -> L_1(gamma) of Federer 2.7.13, p. 130, "such
    that, for each alpha summable function u, beta^x(u)(g x) =
    integral u(g s) d beta s whenever g in G, integral beta^x(u)
    d gamma = integral u d alpha". Definition by these two laws, the
    first for gamma almost all points g x. The hypotheses on alpha,
    beta, gamma belong to the results. *)
Record is_coset_lone_integral (R : realType) (G X : topologicalType) (mul : G -> G -> G)
    (A : G -> X -> X) (x : X) (alpha : set G -> \bar R) (beta : set (isotropy_subgroup A x) -> \bar R)
    (gamma : set X -> \bar R) (B : (G -> R) -> X -> R) : Prop := {
  (** Source for [coset_lone_integral_identity]: "integral beta^x(u)
      d gamma = integral u d alpha", for each alpha summable u,
      Federer 2.7.13, p. 130. *)
  coset_lone_integral_identity : forall u (a : R),
    is_measure_integral alpha (real_total_integrand u) a%:E ->
    is_measure_integral gamma (real_total_integrand (B u)) a%:E;
  (** Source for [coset_lone_integral_fibre]: "beta^x(u)(g x) =
      integral u(g s) d beta s whenever g in G", for each alpha
      summable u and gamma almost all points g x, Federer 2.7.13,
      p. 130, with "gamma[X ~ E(u)] = 0" from the proof. *)
  coset_lone_integral_fibre : forall u, summable_real_functions alpha u ->
    measure_almost_everywhere gamma [set y | coset_fibre_integral mul A x beta u y (B u y)]
}.

Arguments is_coset_lone_integral [R G X] mul A x alpha beta gamma B.
