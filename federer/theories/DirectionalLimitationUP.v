(** Federer (1969), 2.8.9, pp. 145–146: directional limitation and
    controlled families of centers and radii. We specify Federer's original
    condition, with its radial projection points quantified rather than
    assumed to exist. the original strict comparison is retained here. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [metric_extended_open_ball]: the U(a,xi)
    in Federer 2.8.9, pp. 145–146. Xi may be infinity,
    as in the finite-dimensional normed-space example on p. 146.
    The distance itself remains finite. This supporting set
    formula agrees with the previous real-radius open ball. *)
Definition metric_extended_open_ball (R : realType) (X : metricType R)
    (a : X) (xi : \bar R) := [set x | ((mdist a x)%:E < xi)%E].

(** Source for [is_radial_projection_configuration]: the
    distance equations for x in Federer 2.8.9, p. 145:
    rho(a,x)=rho(a,c) and rho(x,b)=rho(a,b)-rho(a,c),
    with rho(a,b)>=rho(a,c). This predicate asserts the
    displayed laws and does not postulate existence or uniqueness. *)
Definition is_radial_projection_configuration (R : realType) (X : metricType R)
    (a b c x : X) :=
  mdist a c <= mdist a b /\ mdist a x = mdist a c /\
    mdist x b = mdist a b - mdist a c.

(** Source for [directionally_separated_from]: the quantified separation
    premise in Federer 2.8.9, p. 145. For each ordered pair of distinct
    members b,c of B, every x satisfying the radial equations has
    rho(x,c)/rho(a,c)>=eta. it is not substituted for this printed
    definition. *)
Definition directionally_separated_from (R : realType) (X : metricType R)
    (a : X) (eta : R) (B : set X) :=
  forall b c, B b -> B c -> b <> c -> forall x,
    is_radial_projection_configuration a b c x ->
    eta <= mdist x c / mdist a c.

(** Source for [is_directionally_limited_at]: the original definition in
    Federer 2.8.9, p. 145, including xi>0, 0<eta<=1/3 and a positive integer
    zeta. Cardinal comparison with the finite ordinal expresses card B<=zeta
    without assuming B finite in advance. *)
Record is_directionally_limited_at (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta : R) (zeta : nat) : Prop := {
  (** Source for [directional_radius_positive]: xi>0 in
      Federer 2.8.9, p. 145; infinity is allowed on p. 146. *)
  directional_radius_positive : (0 < xi)%E;
  (** Source for [directional_separation_range]: the printed
      bounds 0<eta<=1/3 in Federer 2.8.9, p. 145. *)
  directional_separation_range : 0 < eta <= 1/3;
  (** Source for [directional_cardinal_positive]: zeta is
      a positive integer, Federer 2.8.9, p. 145. *)
  directional_cardinal_positive : (0 < zeta)%N;
  (** Source for [directional_cardinal_bound]: the bound on
      every separated B subset (A intersect U(a,xi)) minus
      {a}, Federer 2.8.9, p. 145. *)
  directional_cardinal_bound : forall a, A a -> forall B,
    B `<=` (A `&` metric_extended_open_ball a xi) `\` [set a] ->
    directionally_separated_from a eta B -> B #<= [set: 'I_zeta]
}.

(** Source for [is_positive_radius_family]: the restriction P subset X times
    {r:0<r<infinity} in Federer 2.8.9, p. 146 Coordinates are retained
    because a closed ball need not uniquely determine its center or radius. *)
Definition is_positive_radius_family (R : realType) (X : choiceType)
    (P : set (X * R)) := forall p, P p -> 0 < p.2.

(** Source for [is_controlled_ball_family]: the definition of tau controlled
    P in Federer 2.8.9, p. 146. The comparisons r>s/tau and s>r/tau are
    STRICT as printed. that weaker definition is distinguished from this
    one. *)
Record is_controlled_ball_family (R : realType) (X : metricType R)
    (tau : R) (P : set (X * R)) : Prop := {
  (** Source for [controlled_factor_gt_one]: 1<tau<infinity
      in Federer 2.8.9, p. 146; tau is a real scalar. *)
  controlled_factor_gt_one : 1 < tau;
  (** Source for [controlled_positive_radii]: the domain of
      the radius coordinate, Federer 2.8.9, p. 146. *)
  controlled_positive_radii : is_positive_radius_family P;
  (** Source for [controlled_pair_alternative]: for distinct
      (a,r),(b,s), either rho(a,b)>r>s/tau or
      rho(a,b)>s>r/tau, Federer 2.8.9, p. 146. *)
  controlled_pair_alternative : forall p q, P p -> P q -> p <> q ->
    (p.2 < mdist p.1 q.1 /\ q.2 / tau < p.2) \/
    (q.2 < mdist p.1 q.1 /\ p.2 / tau < q.2)
}.
