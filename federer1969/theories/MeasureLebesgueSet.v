(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  MeasurableDistanceTo MeasureMeanFunction CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lebesgue_set]: direct bracketed definition in
    Federer 2.9.9, p. 156: the set of points x where the mean distance to
    f(x) tends to zero. The existential graph value keeps x in the actual
    domain of f. *)
Definition measure_lebesgue_set (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (f : partial_function X Y) : set X :=
  [set x | exists a, partial_function_graph f x a /\
    partial_function_graph (covering_relation_limit V
      (measure_mean_function phi (partial_distance_to f a))) x 0].

(** Source for [measure_lebesgue_set_domain]: supporting domain
    qualification of Federer's Lebesgue set in 2.9.9, p. 156.
    Undefined values of f do not yield Lebesgue points. *)
Lemma measure_lebesgue_set_domain (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (f : partial_function X Y) :
  measure_lebesgue_set phi V f `<=` partial_function_domain f.
Proof. by move=> x [a [ha _]]; exists a. Qed.
