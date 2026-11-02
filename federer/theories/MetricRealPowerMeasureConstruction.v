(** Private real power-gauge measure witnesses for Federer (1969),
    2.10.2(1), p. 171, used in 2.10.29, pp. 193–195. Apply the previously
    proved opaque Caratheodory operator; expose only the gauge specification
    through a new sealed interface. The coefficient remains explicit; no
    Gamma formula is assumed. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import MetricRealPowerCost MetricRealPowerMeasureUP HausdorffLengthUP CaratheodoryMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [metric_real_power_measure_exists]: supporting
    existence of the real power-gauge measure
    of 2.10.2(1), p. 171, from 2.10.1,
    with arbitrary coefficient c. Mathematical
    measure laws require its stated nonnegativity. *)
Theorem metric_real_power_measure_exists (R : realType) (X : metricType R) (c p : R) :
  exists mu : set X -> \bar R, is_metric_real_power_measure c p mu.
Proof.
exists (@caratheodory_measure R X (@nonempty_metric_sets R X) (fun S=>val S)
  (fun S=>metric_real_diameter_cost c p (val S))).
exact: caratheodory_measure_specification.
Qed.

(** Source for [closed_metric_real_power_measure_exists]: supporting
    independent existence of the closed-cover
    real power-gauge version of 2.10.2(1),
    p. 171. Equality with unrestricted covers
    remains a theorem to prove separately. *)
Theorem closed_metric_real_power_measure_exists (R : realType) (X : metricType R) (c p : R) :
  exists mu : set X -> \bar R, is_closed_metric_real_power_measure c p mu.
Proof.
exists (@caratheodory_measure R X (@nonempty_closed_metric_sets R X) (fun S=>val S)
  (fun S=>metric_real_diameter_cost c p (val S))).
exact: caratheodory_measure_specification.
Qed.
