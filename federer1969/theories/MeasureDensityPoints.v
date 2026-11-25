(** Federer (1969), 2.9.11, p. 158: choose a phi hull of A before comparing
    its density with a characteristic function. Here the original class M
    permits a Borel hull, obtained from finite local hulls on the bounded
    Borel partition. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureRestriction MeasureDerivates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_one_points]: direct set P in Federer 2.9.11,
    p. 158 The arbitrary set A is not assumed measurable. *)
Definition measure_density_one_points (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) : set X :=
  [set x | partial_function_graph (measure_derivate (measure_restrict phi A) phi V) x 1].

(** Source for [measure_density_complement_zero_points]: direct set Q in
    Federer 2.9.11, p. 158 It uses S minus A in the numerator, and requires
    an actual zero limit on the partial division domain. *)
Definition measure_density_complement_zero_points (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) : set X :=
  [set x | partial_function_graph (measure_derivate (measure_restrict phi (~` A)) phi V) x 0].
