(** Federer (1969), Lemma 2.8.10, p. 147: select center-radius pairs with
    center distance larger than the sum of radii and with a sufficiently
    large nearby selected pair for every eligible pair. The auxiliary
    saturated families are the class D in the printed proof. These
    specifications retain Federer's parameter-level statement. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_bounded_positive_radius_family]: the
    hypothesis Q subset X times {r:0<r<mu} in Federer
    2.8.10, p. 147. The separate real bound mu is
    positive in the public theorem, as printed. *)
Definition is_bounded_positive_radius_family (R : realType) (X : choiceType)
    (mu : R) (Q : set (X * R)) := forall p, Q p -> 0 < p.2 < mu.

(** Source for [radius_parameters_separated]: condition (1)
    in Federer 2.8.10, p. 147: distinct (a,r),(b,s)
    have rho(a,b)>r+s. This is stronger than disjointness
    of the associated closed balls in a general metric space. *)
Definition radius_parameters_separated (R : realType) (X : metricType R)
    (P : set (X * R)) :=
  forall p q, P p -> P q -> p <> q -> p.2 + q.2 < mdist p.1 q.1.

(** Source for [is_radius_cover_selection]: the selected
    subset R in Federer 2.8.10, p. 147, specified
    by membership and the two printed conclusions. No
    selected construction is part of this predicate. *)
Record is_radius_cover_selection (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X * R)) : Prop := {
  (** Source for [radius_selection_members]: R is a subset
      of Q, Federer 2.8.10, p. 147. *)
  radius_selection_members : P `<=` Q;
  (** Source for [radius_selection_separated]: condition (1)
      of Federer 2.8.10, p. 147. *)
  radius_selection_separated : radius_parameters_separated P;
  (** Source for [radius_selection_dominates]: condition (2)
      of Federer 2.8.10, p. 147: every (a,r) in Q
      has (b,s) in R with rho(a,b)<=r+s and s>r/tau. *)
  radius_selection_dominates : forall q, Q q -> exists p,
    P p /\ mdist q.1 p.1 <= q.2+p.2 /\ q.2/tau < p.2
}.

(** Source for [is_radius_saturated_family]: the class D
    in the proof of Federer 2.8.10, p. 147. A
    separated P belongs to D when every eligible pair near
    some member is near a sufficiently large member. The
    printed alternative (3) is expressed as an implication. *)
Record is_radius_saturated_family (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X * R)) : Prop := {
  (** Source for [radius_saturated_members]: membership in
      Q for families of class D, Federer 2.8.10, p. 147. *)
  radius_saturated_members : P `<=` Q;
  (** Source for [radius_saturated_separated]: condition (1)
      for families in D, Federer 2.8.10, p. 147. *)
  radius_saturated_separated : radius_parameters_separated P;
  (** Source for [radius_saturated_controls_nearby]: the
      nonvacuous alternative in condition (3) of Federer
      2.8.10, p. 147. *)
  radius_saturated_controls_nearby : forall q p, Q q -> P p ->
    mdist q.1 p.1 <= q.2+p.2 -> exists s,
    P s /\ mdist q.1 s.1 <= q.2+s.2 /\ q.2/tau < s.2
}.
