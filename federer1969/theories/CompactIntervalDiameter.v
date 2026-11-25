(** Federer (1969), 2.10.28(3), p. 192: supporting conversion between the
    finite real mesh of the interval families and the extended diameter in
    the covering infima. All intervals in F are nonempty and compact, but
    may be singletons. The proofs use only endpoint existence and the
    existing abstract diameter laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_interval_diameter_finite_value]:
    supporting finite diameter of each interval
    in the mesh condition of 2.10.28(3),
    p. 192, including zero length. *)
Lemma compact_interval_diameter_finite_value (R : realType) (A : set (real_line_metric R)) :
  is_compact_real_interval A ->
  @extended_metric_diameter R [the metricType R of real_line_metric R] A=
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] A))%:E.
Proof. by move=> [a [b [hab ->]]]; rewrite (extended_metric_diameter_segment hab). Qed.

(** Source for [compact_interval_diameter_nonnegative]: supporting
    nonnegative finite mesh values in 2.10.28(3),
    p. 192, from the ordered endpoints. *)
Lemma compact_interval_diameter_nonnegative (R : realType) (A : set (real_line_metric R)) :
  is_compact_real_interval A ->
  0<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] A).
Proof.
move=> [a [b [hab ->]]]; rewrite (extended_metric_diameter_segment hab).
by change (0<=b-a); rewrite subr_ge0.
Qed.

(** Source for [compact_interval_diameter_bound]: supporting
    real/extended conversion of the cutoff
    bound on each interval in 2.10.28(3),
    p. 192. No finiteness premise beyond
    membership in the printed interval family
    is added. *)
Lemma compact_interval_diameter_bound (R : realType) (A : set (real_line_metric R)) (r : R) :
  is_compact_real_interval A ->
  ((@extended_metric_diameter R [the metricType R of real_line_metric R] A<=r%:E)%E <->
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] A)<=r)%R).
Proof. by move=> hA; rewrite (compact_interval_diameter_finite_value hA) lee_fin. Qed.
