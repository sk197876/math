(** Federer (1969), 2.10.24, p. 188: the integer Hausdorff diameter gauge
    satisfies the compact-cost hypotheses of 2.10.22, p. 184. Nonnegativity,
    Hausdorff continuity and positivity on positive diameters are proved
    from the sealed diameter and the positive normalization of 2.7.16, p.
    135. Degree zero retains singleton cost one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter CompactSetDistanceProfile
  CompactMetricBounded CompactHausdorffMetric CompactGeneratorCostUP CompactGeneratorCostLaws
  HausdorffDiameterCost HausdorffPowerCostLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_compact_generator_cost]: supporting
    finite-real restriction of the Hausdorff gauge in
    2.10.2(1), p. 171, to the compact family
    used for the application in 2.10.24, p. 188. *)
Definition hausdorff_compact_generator_cost (R : realType) (X : metricType R) (m : nat)
    (C : compact_metric_set X) := hausdorff_normalisation R m*(compact_metric_diameter C)^+m.

(** Source for [hausdorff_compact_generator_cost_value]: supporting
    exact cost compatibility for 2.10.24, p. 188.
    Compactness makes the diameter finite; this is
    a proved identification with the original extended gauge. *)
Lemma hausdorff_compact_generator_cost_value (R : realType) (X : metricType R) (m : nat)
    (C : compact_metric_set X) :
  hausdorff_diameter_cost m (val C)=(hausdorff_compact_generator_cost m C)%:E.
Proof. by rewrite /hausdorff_diameter_cost compact_metric_diameter_finite_value hausdorff_power_cost_finite. Qed.

(** Source for [hausdorff_compact_generator_cost_laws]: supporting
    verification of all 2.10.22 cost hypotheses for
    the Hausdorff application in 2.10.24, p. 188.
    The integer-degree restriction matches the project's
    Hausdorff measure definition; degree zero is included. *)
Theorem hausdorff_compact_generator_cost_laws (R : realType) (X : metricType R) (m : nat) :
  is_continuous_positive_compact_cost (@hausdorff_compact_generator_cost R X m).
Proof.
have hd0 (C : compact_metric_set X) : 0<=compact_metric_diameter C.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification (val C)).
  by rewrite compact_metric_diameter_finite_value lee_fin in hh.
have hnorm := @hausdorff_normalisation_positive R m.
have hpower : forall n, continuous (fun C : compact_hausdorff_space X => ((compact_metric_diameter C)^+n : R^o)).
  elim=> [|n IH] C.
  - have he : (fun D : compact_hausdorff_space X => ((compact_metric_diameter D)^+0 : R^o))=
        (fun _ : compact_hausdorff_space X => (1 : R^o)) by apply: funext=> D; rewrite expr0.
    rewrite he; exact: (@cvg_cst [the topologicalType of R^o] 1%R
      [the topologicalType of compact_hausdorff_space X] (nbhs C) (nbhs_filter C)).
  - have he : (fun D : compact_hausdorff_space X => ((compact_metric_diameter D)^+n.+1 : R^o))=
      (fun D : compact_hausdorff_space X => compact_metric_diameter D*(compact_metric_diameter D)^+n).
      by apply: funext=> D; rewrite exprS.
    rewrite he; exact: cvgM (@compact_diameter_map_continuous R X C) (IH C).
constructor.
- move=> C; apply: mulr_ge0 (ltW hnorm) _; exact: exprn_ge0 (hd0 C).
- move=> C.
  have hconstant := @cvg_cst [the topologicalType of R^o] (hausdorff_normalisation R m)
    [the topologicalType of compact_hausdorff_space X] (nbhs C) (nbhs_filter C).
  exact: cvgM hconstant (hpower m C).
- move=> C hdiam; apply: mulr_gt0 hnorm _; exact: exprn_gt0 hdiam.
Qed.
