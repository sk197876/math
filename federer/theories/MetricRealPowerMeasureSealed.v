(** Opaque real power-gauge measures for Federer (1969), 2.10.2(1), p. 171,
    supporting 2.10.29, pp. 193–195. Expose only the unrestricted and
    closed-cover specifications. The positive normalising coefficient is
    explicit. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricRealPowerMeasureUP MetricRealPowerMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type METRIC_REAL_POWER_MEASURE.
(** Source for [value]: abstract unrestricted
    real power-gauge measure of 2.10.2(1),
    p. 171, with coefficient c explicit. *)
Parameter value : forall (R : realType) (X : metricType R), R -> R -> set X -> \bar R.
(** Source for [closed_value]: independently specified
    closed-cover version in 2.10.2(1), p. 171. *)
Parameter closed_value : forall (R : realType) (X : metricType R), R -> R -> set X -> \bar R.
(** Source for [laws]: unrestricted covering laws
    of 2.10.2(1), p. 171. *)
Parameter laws : forall (R : realType) (X : metricType R) (c p : R),
  is_metric_real_power_measure c p (@value R X c p).
(** Source for [closed_laws]: closed covering laws
    of 2.10.2(1), p. 171. *)
Parameter closed_laws : forall (R : realType) (X : metricType R) (c p : R),
  is_closed_metric_real_power_measure c p (@closed_value R X c p).
End METRIC_REAL_POWER_MEASURE.

Module MetricRealPowerMeasure : METRIC_REAL_POWER_MEASURE.
(** Source for [value]: proved unrestricted witness
    for 2.10.2(1), p. 171, hidden
    by opaque module ascription. *)
Definition value (R : realType) (X : metricType R) (c p : R) :=
  projT1 (cid (@metric_real_power_measure_exists R X c p)).
(** Source for [closed_value]: proved closed-cover
    witness for 2.10.2(1), p. 171,
    hidden by opaque module ascription. *)
Definition closed_value (R : realType) (X : metricType R) (c p : R) :=
  projT1 (cid (@closed_metric_real_power_measure_exists R X c p)).
(** Source for [laws]: unrestricted specification
    supplied by the proved witness supporting
    2.10.2(1), p. 171. *)
Lemma laws (R : realType) (X : metricType R) (c p : R) :
  is_metric_real_power_measure c p (@value R X c p).
Proof. exact: (projT2 (cid (@metric_real_power_measure_exists R X c p))). Qed.
(** Source for [closed_laws]: closed specification
    supplied by the proved witness supporting
    2.10.2(1), p. 171. *)
Lemma closed_laws (R : realType) (X : metricType R) (c p : R) :
  is_closed_metric_real_power_measure c p (@closed_value R X c p).
Proof. exact: (projT2 (cid (@closed_metric_real_power_measure_exists R X c p))). Qed.
End MetricRealPowerMeasure.
