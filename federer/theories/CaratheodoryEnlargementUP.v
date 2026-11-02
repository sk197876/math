(** Controlled enlargements for Federer (1969), 2.10.18, p. 180, and its
    proof. These are conditional laws, not axioms; the printed enlargement
    will supply a witness. Positive finite generator cost follows from
    Federer's strict growth condition and retains his original partial
    quotient. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter DiameterEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_caratheodory_enlargement]: supporting specification for
    the fine enlarged generators in the proof of 2.10.18(1), p. 180 The
    auxiliary constant k controls diameter and cost simultaneously;
    Federer's printed enlargement has diameter factor five. *)
Record is_caratheodory_enlargement (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k : R) : Prop := {
  (** Source for [caratheodory_enlargement_constant_positive]: supporting
      positive control constant for 2.10.18(1), p. 180. *)
  caratheodory_enlargement_constant_positive : (0<k)%R;
  (** Source for [caratheodory_enlargement_cost_positive]: consequence
      of the strict cost-growth condition in 2.10.18, p. 180. *)
  caratheodory_enlargement_cost_positive : forall S, F S -> 0<c S;
  (** Source for [caratheodory_enlargement_cost_finite]: consequence
      of the finite growth bound in 2.10.18, p. 180. *)
  caratheodory_enlargement_cost_finite : forall S, F S -> c S < +oo;
  (** Source for [caratheodory_enlargement_member]: the enlarged
      set is a generator on which zeta is defined in
      2.10.18, p. 180; explicit domain interpretation. *)
  caratheodory_enlargement_member : forall S, F S -> F (E S);
  (** Source for [caratheodory_enlargement_contains]: Supporting Federer
    2.10.18(1), p. 180. *)
  caratheodory_enlargement_contains : forall S, F S -> diameter_enlargement F S `<=` E S;
  (** Source for [caratheodory_enlargement_diameter]: supporting
    small-diameter control in 2.10.18(1), p. 180 *)
  caratheodory_enlargement_diameter : forall S, F S ->
    extended_metric_diameter (E S)<=k%:E*extended_metric_diameter S;
  (** Source for [caratheodory_enlargement_cost]: supporting
      non-strict enlargement-cost estimate in the proof of
      2.10.18(1), p. 180; implied by the printed strict bound. *)
  caratheodory_enlargement_cost : forall S, F S -> c (E S)<=k%:E*c S
}.
