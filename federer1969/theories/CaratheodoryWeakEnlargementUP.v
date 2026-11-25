(** Containing-generator enlargement for the spherical consequences of
    Federer (1969), 2.10.19(3)–(5), p. 181. They introduce no project
    axioms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter DiameterEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_weak_caratheodory_enlargement]: supporting weak
    containing-generator laws for 2.10.19(3)–(5), p. 181 Zero costs are
    allowed and cost finiteness is not silently assumed. This is an
    additional specification, distinct from Federer's stronger printed
    2.10.18. *)
Record is_weak_caratheodory_enlargement (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k : R) : Prop := {
  (** Source for [weak_enlargement_constant_positive]: supporting positive
    enlargement constant in 2.10.19, p. 181 *)
  weak_enlargement_constant_positive : (0<k)%R;
  (** Source for [weak_enlargement_cost_nonnegative]: supporting nonnegative
    costs for 2.10.19, p. 181 *)
  weak_enlargement_cost_nonnegative : forall S, F S -> 0<=c S;
  (** Source for [weak_enlargement_member]: supporting containing generator
    for 2.10.19, p. 181 *)
  weak_enlargement_member : forall S, F S -> F (E S);
  (** Source for [weak_enlargement_contains]: supporting inclusion hat S
    subset S-prime in the spherical proof for 2.10.19, p. 181 *)
  weak_enlargement_contains : forall S, F S -> diameter_enlargement F S `<=` E S;
  (** Source for [weak_enlargement_diameter]: supporting diameter control for
    2.10.19, p. 181 *)
  weak_enlargement_diameter : forall S, F S ->
    extended_metric_diameter (E S)<=k%:E*extended_metric_diameter S;
  (** Source for [weak_enlargement_cost]: supporting weak cost growth for
    2.10.19, p. 181 *)
  weak_enlargement_cost : forall S, F S -> c (E S)<=k%:E*c S
}.
