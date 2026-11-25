(** Federer (1969), 2.10.2(1), p. 171: public real power-gauge measures with
    an explicit coefficient, used for the real exponent estimates of
    2.10.29, pp. 193–195. Definitions use only the opaque specifications; no
    Euler-Gamma normalisation is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricRealPowerMeasureUP MetricRealPowerMeasureLaws MetricRealPowerMeasureSealed
  MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.

(** Source for [metric_real_power_measure]: public
    unrestricted real power-gauge measure for
    2.10.2(1), p. 171, with coefficient
    c explicit. The implementation is opaque. *)
Definition metric_real_power_measure (R : realType) (X : metricType R) (c p : R) :=
  @MetricRealPowerMeasure.value R X c p.

(** Source for [closed_metric_real_power_measure]: public
    independently specified closed-cover version
    of 2.10.2(1), p. 171. *)
Definition closed_metric_real_power_measure (R : realType) (X : metricType R) (c p : R) :=
  @MetricRealPowerMeasure.closed_value R X c p.

(** Source for [metric_real_power_measure_specification]: direct
    unrestricted power-gauge covering laws in
    2.10.2(1), p. 171, from the sealed interface. *)
Lemma metric_real_power_measure_specification (R : realType) (X : metricType R) (c p : R) :
  is_metric_real_power_measure c p (@metric_real_power_measure R X c p).
Proof. exact: MetricRealPowerMeasure.laws. Qed.

(** Source for [closed_metric_real_power_measure_specification]:
    direct closed power-gauge covering laws in
    2.10.2(1), p. 171, from the sealed interface. *)
Lemma closed_metric_real_power_measure_specification (R : realType) (X : metricType R) (c p : R) :
  is_closed_metric_real_power_measure c p (@closed_metric_real_power_measure R X c p).
Proof. exact: MetricRealPowerMeasure.closed_laws. Qed.

(** Source for [metric_real_power_measure_is_measure]: direct
    measure law for the real power gauge
    of 2.10.2(1), p. 171, with c>=0. *)
Lemma metric_real_power_measure_is_measure (R : realType) (X : metricType R) (c p : R) :
  0<=c -> is_measure (@metric_real_power_measure R X c p).
Proof. move=> hc; exact: metric_real_power_measure_law hc (metric_real_power_measure_specification X c p). Qed.
