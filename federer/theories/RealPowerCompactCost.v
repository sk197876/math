(** Federer (1969), 2.10.47, p. 205, uses the compact-cutoff continuity of
    2.10.20, p. 182. Verify the continuous compact-cost hypotheses for real
    positive power gauges, as in the Hausdorff application of 2.10.24, p.
    188. The coefficient is explicit; no Gamma normalisation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter CompactSetDistanceProfile
  CompactMetricBounded CompactHausdorffMetric CompactGeneratorCostUP CompactGeneratorCostLaws
  MetricRealPowerCost RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [real_power_compact_generator_cost]: supporting
    restriction of the diameter gauge to nonempty compact
    generators, 2.10.24, p. 188, used in
    the final step of 2.10.47, p. 205. *)
Definition real_power_compact_generator_cost (R : realType) (X : metricType R) (c p : R)
    (C : compact_metric_set X) := c*real_power (compact_metric_diameter C) p.

(** Source for [real_power_compact_generator_cost_value]: supporting
    exact agreement of finite compact cost with the
    original gauge in 2.10.47, p. 205. *)
Lemma real_power_compact_generator_cost_value (R : realType) (X : metricType R) (c p : R)
    (C : compact_metric_set X) :
  metric_real_diameter_cost c p (val C)=(real_power_compact_generator_cost c p C)%:E.
Proof. by rewrite /metric_real_diameter_cost compact_metric_diameter_finite_value metric_real_power_cost_finite. Qed.

(** Source for [real_power_compact_generator_cost_laws]: supporting
    real-degree verification of the compact-cost hypotheses
    used in 2.10.47, p. 205. Both coefficient
    and degree are positive; the compact set may be a
    singleton, with cost zero. *)
Theorem real_power_compact_generator_cost_laws (R : realType) (X : metricType R) (c p : R) :
  0<c -> 0<p -> is_continuous_positive_compact_cost (@real_power_compact_generator_cost R X c p).
Proof.
move=> hc hp.
have hd0 (C : compact_metric_set X) : 0<=compact_metric_diameter C.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification (val C)).
  by rewrite compact_metric_diameter_finite_value lee_fin in hh.
have hpower := @real_power_continuous_comp R (compact_hausdorff_space X)
  (@compact_metric_diameter R X) p (@compact_diameter_map_continuous R X) hd0 hp.
constructor.
- move=> C; exact: mulr_ge0 (ltW hc) (real_power_nonnegative _ _).
- move=> C.
  have hconstant := @cvg_cst [the topologicalType of R^o] c
    [the topologicalType of compact_hausdorff_space X] (nbhs C) (nbhs_filter C).
  exact: cvgM hconstant (hpower C).
- move=> C hdiam; exact: mulr_gt0 hc (real_power_strictly_positive p hdiam).
Qed.
