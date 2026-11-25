(** Federer (1969), 2.3.6, p. 77: the range reduction applies to both cases
    of Lusin's theorem. We expose the common approximation property with the
    class P of permitted source subsets (closed or compact). Source context:
    MeasurableFiniteImageSupport.v. This is a proved property, not an
    additional measure or topology axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_lusin_approximation]: supporting abstract
    common conclusion of Federer 2.3.5, pp. 76–77, for
    transfer to the Ulam-dense targets of 2.3.6, p. 77. *)
Definition has_lusin_approximation (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (P : set (set X)) :=
  forall (Y : metricType R) (D : set Y), countable D -> dense D ->
  forall (f : partial_function X Y), is_measure_measurable_function mu f ->
  forall A, measure_measurable mu A -> mu A < +oo -> forall e : R, (0 < e)%R ->
  exists C, P C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f.
