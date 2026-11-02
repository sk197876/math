(** Public Banach space E of all bounded real valued continuous functions on
    a metric space Y, with the norm nu(f) = sup im |f|, Federer (1969),
    2.5.16, p. 110. The space, its evaluation and its norm come from the
    sealed interface BoundedContinuousSpaceSealed.v; the norm laws and the
    completeness are derived in BoundedContinuousSpaceLaws.v from the
    abstract specification alone. Source context:
    BoundedContinuousSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP BoundedContinuousSpaceUP
  BoundedContinuousSpaceLaws BoundedContinuousSpaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [bounded_continuous_space]: the vector space E of
    Federer 2.5.16, p. 110. *)
Definition bounded_continuous_space (R : realType) (Y : metricType R) : lmodType R :=
  @BoundedContinuousSpace.space R Y.

(** Source for [bounded_continuous_evaluate]: evaluation of the
    members of E as real valued functions on Y, Federer 2.5.16, p. 110. *)
Definition bounded_continuous_evaluate (R : realType) (Y : metricType R)
    (f : bounded_continuous_space Y) : Y -> R := @BoundedContinuousSpace.value R Y f.

(** Source for [bounded_continuous_space_norm]: the norm
    nu(f) = sup im |f| of Federer 2.5.16, p. 110. *)
Definition bounded_continuous_space_norm (R : realType) (Y : metricType R)
    (f : bounded_continuous_space Y) : R := @BoundedContinuousSpace.norm R Y f.

(** Source for [bounded_continuous_space_specification]: the abstract
    laws of E and nu, Federer 2.5.16, p. 110, supplied by the sealed
    existence proof. *)
Theorem bounded_continuous_space_specification (R : realType) (Y : metricType R) :
  is_bounded_continuous_space (@bounded_continuous_evaluate R Y) (@bounded_continuous_space_norm R Y).
Proof. exact: (@BoundedContinuousSpace.laws R Y). Qed.

(** Source for [bounded_continuous_space_norm_laws]: nu is a norm on
    E, Federer 2.5.16, p. 110, in the sense of 1.10.5, pp. 47–48. *)
Definition bounded_continuous_space_norm_laws (R : realType) (Y : metricType R) :
  is_real_norm (@bounded_continuous_space_norm R Y) :=
  bounded_continuous_norm_laws (@bounded_continuous_space_specification R Y).

(** Source for [bounded_continuous_space_banach]: "the Banach space E
    of all bounded real valued continuous functions on Y with the norm
    nu(f) = sup im |f|", Federer 2.5.16, p. 110: E is complete for
    the metric induced by nu, in the sense of 2.2.8, p. 64. *)
Theorem bounded_continuous_space_banach (R : realType) (Y : metricType R) :
  is_complete_metric_space
    [the metricType R of real_norm_metric_space (@bounded_continuous_space_norm_laws R Y)].
Proof. exact (@bounded_continuous_space_complete R Y _ _ _ (@bounded_continuous_space_specification R Y)). Qed.
