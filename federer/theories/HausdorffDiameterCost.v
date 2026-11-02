(** Federer (1969), 2.10.2, p. 171, first display: for a nonnegative integer
    m the cost of a nonempty set is alpha(m) times 2 to the power -m times
    its diameter to the power m. The normalization alpha(m) is the unit ball
    volume of 2.7.16(1), p. 135. This file treats that printed
    integer-degree definition, including degree zero and the conventions
    0^0=infinity^0=1. The optional real-degree Gamma normalization is a
    separate extension. No relevant correction in the local Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanBallVolume MetricDiameterUP MetricDiameter
  MetricDiameterClosure ExtendedSupremumPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_normalisation]: direct coefficient
    alpha(m) 2^(-m) in Federer 2.10.2, p. 171, for
    integer m, with alpha(m) from 2.7.16(1), p. 135.
    Division by the positive real 2^m expresses the same value. *)
Definition hausdorff_normalisation (R : realType) (m : nat) : R :=
  euclidean_unit_ball_volume R m / (2 : R)^+m.

(** Source for [hausdorff_power_cost]: supporting numerical
    form of the gauge in Federer 2.10.2, p. 171.
    The extended natural power retains infinity^0=1. *)
Definition hausdorff_power_cost (R : realType) (m : nat) (d : \bar R) : \bar R :=
  ((hausdorff_normalisation R m)%:E * d^+m)%E.

(** Source for [hausdorff_diameter_cost]: direct gauge on
    nonempty sets in Federer 2.10.2, p. 171. The
    formula is also defined on the empty set as supporting
    notation; the actual generator families exclude that set. *)
Definition hausdorff_diameter_cost (R : realType) (X : metricType R)
    (m : nat) (A : set X) : \bar R := hausdorff_power_cost m (extended_metric_diameter A).

(** Source for [hausdorff_normalisation_positive]: supporting
    positive finite coefficient for the cost in Federer
    2.10.2, p. 171, by the unit-ball-volume bounds of
    2.7.16(1), p. 135. *)
Lemma hausdorff_normalisation_positive (R : realType) (m : nat) :
  0<@hausdorff_normalisation R m.
Proof.
rewrite /hausdorff_normalisation divr_gt0 //; first exact: (euclidean_unit_ball_volumeE R m).2.
by rewrite exprn_gt0 // ltr0n.
Qed.

(** Source for [hausdorff_normalisation_zero]: degree-zero normalization in
    Federer 2.10.2(1), p. 171, using alpha(0)=1 from 2.7.16(1), p. 135 *)
Lemma hausdorff_normalisation_zero (R : realType) : @hausdorff_normalisation R 0 = 1.
Proof. by rewrite /hausdorff_normalisation euclidean_unit_ball_volume0 expr0 divr1. Qed.

(** Source for [hausdorff_normalisation_one]: recovery of
    the diameter cost for Hausdorff length in Federer
    2.10.2(1), p. 171, using alpha(1)=2 from
    2.7.16(1), p. 135. *)
Lemma hausdorff_normalisation_one (R : realType) : @hausdorff_normalisation R 1 = 1.
Proof.
by rewrite /hausdorff_normalisation euclidean_unit_ball_volume1 expr1 divff ?pnatr_eq0.
Qed.

(** Source for [hausdorff_diameter_cost_nonnegative]: supporting
    nonnegative gauge hypothesis in Federer 2.10.2, p. 171,
    for the construction of 2.10.1. *)
Lemma hausdorff_diameter_cost_nonnegative (R : realType) (X : metricType R)
    (m : nat) (A : set X) : (0<=hausdorff_diameter_cost m A)%E.
Proof.
rewrite /hausdorff_diameter_cost /hausdorff_power_cost; apply: mule_ge0.
- rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R m).
- apply: expe_ge0; exact: metric_diameter_nonnegative (extended_metric_diameter_specification A).
Qed.

(** Source for [hausdorff_diameter_cost_zero_degree]: every nonempty
    generator has cost one in Federer 2.10.2(1), p. 171, at degree zero This
    includes generators with zero or infinite diameter, so no special
    singleton convention is substituted. *)
Lemma hausdorff_diameter_cost_zero_degree (R : realType) (X : metricType R) (A : set X) :
  hausdorff_diameter_cost 0 A = 1%E.
Proof. by rewrite /hausdorff_diameter_cost /hausdorff_power_cost hausdorff_normalisation_zero expe0 mule1. Qed.

(** Source for [hausdorff_diameter_cost_one_degree]: the
    integer-degree family specializes exactly to the previously
    formalised Hausdorff length in Federer 2.10.2(1), p. 171. *)
Lemma hausdorff_diameter_cost_one_degree (R : realType) (X : metricType R) (A : set X) :
  hausdorff_diameter_cost 1 A=extended_metric_diameter A.
Proof. by rewrite /hausdorff_diameter_cost /hausdorff_power_cost hausdorff_normalisation_one expeS expe0 mule1 mul1e. Qed.

(** Source for [hausdorff_diameter_cost_monotone]: supporting
    comparison of covering costs in Federer 2.10.2(1),
    p. 171, from inclusion and monotonicity of diameter. *)
Lemma hausdorff_diameter_cost_monotone (R : realType) (X : metricType R)
    (m : nat) (A B : set X) : A `<=` B ->
  (hausdorff_diameter_cost m A<=hausdorff_diameter_cost m B)%E.
Proof.
move=> hAB; rewrite /hausdorff_diameter_cost /hausdorff_power_cost.
apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R m).
exact: nonnegative_extended_power_monotone
  (metric_diameter_nonnegative (extended_metric_diameter_specification A))
  (extended_metric_diameter_mono hAB).
Qed.

(** Source for [hausdorff_diameter_cost_closure]: direct unchanged-cost step
    for the closed-cover alternative in Federer 2.10.2(1), p. 171 Empty and
    unbounded sets are included in this supporting identity. *)
Lemma hausdorff_diameter_cost_closure (R : realType) (X : metricType R)
    (m : nat) (A : set X) : hausdorff_diameter_cost m (closure A)=hausdorff_diameter_cost m A.
Proof. by rewrite /hausdorff_diameter_cost extended_metric_diameter_closure. Qed.
