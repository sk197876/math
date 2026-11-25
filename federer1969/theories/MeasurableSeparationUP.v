(** Federer (1969), 2.3.2(7)–(9), pp. 74–75: the separation inequalities for
    numerical and metric-valued functions and for measures on metric spaces.
    The metric condition is expressed as a positive uniform lower bound on
    cross distances, including empty sets; this is the order-law form of a
    strictly positive extended-real infimum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_level_separated]: direct inequality
    in Federer 2.3.2(7), p. 74. The two thresholds are
    finite real numbers a < b; values of f may be infinite. *)
Definition is_measure_level_separated (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :=
  forall (T : set X) (a b : R), (a < b)%R ->
    mu (T `&` partial_function_preimage f [set y | y <= a%:E]) +
    mu (T `&` partial_function_preimage f [set y | b%:E <= y]) <= mu T.

(** Source for [metric_sets_positively_separated]: supporting
    order-law formulation of the positive-distance premise in
    Federer 2.3.2(8)–(9), pp. 74–75. A positive real
    uniformly bounds all cross distances from below. *)
Definition metric_sets_positively_separated (R : realType) (Y : metricType R)
    (A B : set Y) := exists delta : R, (0 < delta)%R /\
      forall x, A x -> forall y, B y -> (delta <= mdist x y)%R.

(** Source for [is_measure_image_separated]: direct inequality
    in Federer 2.3.2(8), p. 74, using the uniform
    lower-bound formulation of positive distance. No measurability
    of the separated image sets A and B is assumed. *)
Definition is_measure_image_separated (R : realType) (X : choiceType) (Y : metricType R)
    (mu : set X -> \bar R) (f : partial_function X Y) :=
  forall (T : set X) (A B : set Y), metric_sets_positively_separated A B ->
    mu (T `&` partial_function_preimage f A) +
    mu (T `&` partial_function_preimage f B) <= mu T.

(** Source for [is_metric_separated_measure]: direct additivity
    lower bound in Caratheodory's criterion, Federer 2.3.2(9),
    p. 75. Ordinary subadditivity supplies the reverse inequality. *)
Definition is_metric_separated_measure (R : realType) (X : metricType R)
    (mu : set X -> \bar R) :=
  forall A B, metric_sets_positively_separated A B -> mu A + mu B <= mu (A `|` B).
