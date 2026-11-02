(** Public corrected topological construction supporting Federer (1969),
    2.10.1, p. 170. The selected object is opaque. Its measure law and
    continuous-map measurability are proved from the abstract
    whole-space-open-cover supremum specification. Source context and
    distinction from the refuted literal printed extension:
    TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import TopologicalCaratheodoryUP TopologicalCaratheodorySealed
  TopologicalCaratheodoryMeasure TopologicalContinuousMeasurability MeasureUP
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [topological_caratheodory_measure]: public
    corrected topological construction supporting Federer
    2.10.1, p. 170, through its sealed specification. *)
Definition topological_caratheodory_measure (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :=
  @TopologicalCaratheodory.value R X J S cost.

(** Source for [topological_caratheodory_specification]: public
    abstract whole-space-cover supremum laws for the corrected
    version supporting Federer 2.10.1, p. 170. *)
Lemma topological_caratheodory_specification (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  is_topological_caratheodory S cost (topological_caratheodory_measure S cost).
Proof. exact: TopologicalCaratheodory.laws. Qed.

(** Source for [topological_caratheodory_measure_is_measure]:
    public corrected arbitrary-topological measure assertion
    supporting Federer 2.10.1, p. 170. *)
Theorem topological_caratheodory_measure_is_measure (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  (forall j, 0<=cost j) -> is_measure (topological_caratheodory_measure S cost).
Proof. exact: topological_caratheodory_is_measure (topological_caratheodory_specification S cost). Qed.

(** Source for [topological_caratheodory_measure_continuous_maps]:
    public corrected measurability conclusion supporting
    Federer 2.10.1, p. 170. Every continuous map to an
    arbitrary metric target is measurable for the constructed
    measure; no source separation axiom is added. *)
Theorem topological_caratheodory_measure_continuous_maps (R : realType) (X : topologicalType)
    (Y : metricType R) (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (f : X -> Y) : (forall j, 0<=cost j) -> continuous f ->
  is_measure_measurable_function (topological_caratheodory_measure S cost) (partial_function_total f).
Proof. exact: topological_caratheodory_continuous_measurable (topological_caratheodory_specification S cost). Qed.
