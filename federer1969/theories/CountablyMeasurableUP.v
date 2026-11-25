(** Federer (1969), 2.3.4, p. 76: countably measurable sets and functions.
    For functions the only vector-space datum used is zero; we expose it as
    a distinguished target point. Taking the zero of a topological vector
    space recovers exactly the printed definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_countably_measurable]: direct first definition of
    Federer 2.3.4, p. 76, as a union of a countable family of measurable
    finite-measure sets. The empty family is permitted. *)
Definition measure_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) :=
  exists C : set (set X), countable C /\ A = \bigcup_(B in C) B /\
    forall B, C B -> measure_measurable mu B /\ mu B < +oo.

(** Source for [partial_function_nonzero_locus]: direct set
    of points with nonzero defined function value in the second
    paragraph of Federer 2.3.4, p. 76. Undefined points
    are not assigned a value or included in this locus. *)
Definition partial_function_nonzero_locus (X Y : Type) (zero : Y) (f : partial_function X Y) :=
  partial_function_preimage f [set y | y <> zero].

(** Source for [is_countably_measure_measurable_function]: direct function
    definition in Federer 2.3.4, p. 76 *)
Record is_countably_measure_measurable_function (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (zero : Y) (f : partial_function X Y) : Prop := {
  (** Source for [countably_measurable_function_measurable]: the
      measurability clause of Federer 2.3.4, p. 76. *)
  countably_measurable_function_measurable : is_measure_measurable_function mu f;
  (** Source for [countably_measurable_function_locus]: the countably
      measurable nonzero-locus clause of Federer 2.3.4, p. 76. *)
  countably_measurable_function_locus : measure_countably_measurable mu (partial_function_nonzero_locus zero f)
}.
