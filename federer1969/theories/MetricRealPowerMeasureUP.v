(** Federer (1969), 2.10.2(1), p. 171, real-degree covering definition
    supporting 2.10.29, pp. 193–195. Specify the measure by the Caratheodory
    laws for the stated real power diameter gauge; leave its positive
    coefficient explicit. This is a parameterised gauge measure, before
    identifying Federer's Euler-Gamma normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricRealPowerCost HausdorffLengthUP CaratheodoryLimitUP CaratheodoryLimitUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_metric_real_power_measure]: direct
    abstract real power-gauge covering laws of
    2.10.2(1), p. 171, with coefficient
    c explicit. No product, finiteness or
    dimension-comparison conclusion is assumed. *)
Definition is_metric_real_power_measure (R : realType) (X : metricType R) (c p : R)
    (mu : set X -> \bar R) :=
  @is_caratheodory_limit R X (@nonempty_metric_sets R X) (fun S=>val S)
    (fun S=>metric_real_diameter_cost c p (val S)) mu.

(** Source for [is_closed_metric_real_power_measure]: direct
    independent closed nonempty generator variant
    in 2.10.2(1), p. 171, before proving
    its equality with unrestricted covers. *)
Definition is_closed_metric_real_power_measure (R : realType) (X : metricType R) (c p : R)
    (mu : set X -> \bar R) :=
  @is_caratheodory_limit R X (@nonempty_closed_metric_sets R X) (fun S=>val S)
    (fun S=>metric_real_diameter_cost c p (val S)) mu.

(** Source for [metric_real_power_measure_unique]: supporting
    uniqueness from the covering laws of
    2.10.2(1), p. 171, before selecting
    an opaque implementation of the measure. *)
Lemma metric_real_power_measure_unique (R : realType) (X : metricType R) (c p : R)
    (mu nu : set X -> \bar R) :
  is_metric_real_power_measure c p mu -> is_metric_real_power_measure c p nu ->
  forall A, mu A=nu A.
Proof. exact: caratheodory_limit_unique. Qed.
