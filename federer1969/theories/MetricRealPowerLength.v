(** Federer (1969), 2.10.2(1), p. 171: verify degree-zero and degree-one
    compatibility of the parameterised real power-gauge measure with the
    existing Hausdorff interfaces. Their normalising coefficients are one.
    This supplies concrete integer-degree interpretations for the fractional
    Cantor product example of 2.10.29, pp. 193–195, without an Euler-Gamma
    identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedPositivePower MetricDiameterUP MetricDiameter MetricRealPowerCost
  MetricRealPowerMeasureUP MetricRealPowerMeasure HausdorffLengthUP HausdorffLength
  HausdorffDiameterCost HausdorffMeasureUP HausdorffMeasure CaratheodoryLimitUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_diameter_cost_length]: direct
    unit normalisation at degree one in
    2.10.2(1), p. 171. The cost is
    the actual diameter, including zero
    and positive infinity. *)
Lemma metric_real_diameter_cost_length (R : realType) (X : metricType R) (A : set X) :
  metric_real_diameter_cost 1%R 1%R A=extended_metric_diameter A.
Proof.
rewrite /metric_real_diameter_cost /metric_real_power_cost /extended_metric_real_power oner_eq0 /= mul1e.
exact (@extended_positive_power_one R _ (metric_diameter_nonnegative (extended_metric_diameter_specification A))).
Qed.

(** Source for [metric_real_power_measure_length_agreement]: direct
    degree-one compatibility in 2.10.2(1),
    p. 171, from equality of the stated
    costs and the two independent opaque
    Caratheodory specifications. No Euclidean
    dimension or target measurability is required. *)
Theorem metric_real_power_measure_length_agreement (R : realType) (X : metricType R) :
  forall A, @metric_real_power_measure R X 1%R 1%R A=@hausdorff_length R X A.
Proof.
have hm := @metric_real_power_measure_specification R X 1%R 1%R.
have hcost : (fun S : @nonempty_metric_sets R X=>metric_real_diameter_cost 1%R 1%R (val S))=
    (fun S=>extended_metric_diameter (val S)).
  apply: funext=> S; exact: metric_real_diameter_cost_length.
rewrite /is_metric_real_power_measure hcost in hm.
exact (@hausdorff_length_unique R X _ _ hm (@hausdorff_length_specification R X)).
Qed.

(** Source for [metric_real_power_measure_zero_agreement]: direct
    degree-zero compatibility in 2.10.2(1),
    p. 171, retaining 0^0=infinity^0=1.
    Both old and real-degree models give
    constant unit cost on every nonempty
    generator, so their measures agree. *)
Theorem metric_real_power_measure_zero_agreement (R : realType) (X : metricType R) :
  forall A, @metric_real_power_measure R X 1%R 0%R A=@hausdorff_measure R X 0 A.
Proof.
have hm := @metric_real_power_measure_specification R X 1%R 0%R.
have hn := @hausdorff_measure_specification R X 0.
have hcost : (fun S : @nonempty_metric_sets R X=>metric_real_diameter_cost 1%R 0%R (val S))=
    (fun S=>hausdorff_diameter_cost 0 (val S)).
  apply: funext=> S.
  by rewrite /metric_real_diameter_cost metric_real_power_cost_degree_zero hausdorff_diameter_cost_zero_degree.
rewrite /is_metric_real_power_measure hcost in hm.
exact (@caratheodory_limit_unique R X (@nonempty_metric_sets R X) _ _ _ _ hm hn).
Qed.
