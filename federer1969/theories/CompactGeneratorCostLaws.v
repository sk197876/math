(** Federer (1969), 2.10.22, pp. 184–185: zero costs have zero diameter, and
    small costs force small diameters uniformly on a compact Hausdorff
    family. The latter expands the printed compactness argument for the
    limit generators D_k. It does not assume monotonicity of the cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  HausdorffDiameter RealMetricBackground CompactMaximum CompactGeneratorCostUP NormMetricScaleContinuity
  MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_zero_diameter]: supporting
    zero-cost boundary in the countable-cover argument
    of 2.10.22, pp. 184–185. Positive diameter
    is excluded by the printed positivity hypothesis. *)
Lemma compact_cost_zero_diameter (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost) C :
  cost C=0 -> compact_metric_diameter C=0.
Proof.
move=> hz.
have h0 : 0<=compact_metric_diameter C.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification (val C)).
  by rewrite compact_metric_diameter_finite_value lee_fin in hh.
apply/eqP; rewrite eq_le h0 andbT.
case: (leP (compact_metric_diameter C) 0)=> // hp.
have hh := @compact_cost_positive_diameter_law R X cost hc C hp; by rewrite hz ltxx in hh.
Qed.

(** Source for [compact_diameter_map_continuous]: supporting
    continuity of diameter on the Hausdorff family in
    2.10.22, pp. 184–185, from the two-
    Lipschitz assertion of 2.10.21, p. 183. *)
Lemma compact_diameter_map_continuous (R : realType) (X : metricType R) :
  continuous (fun C : compact_hausdorff_space X => (compact_metric_diameter C : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of compact_hausdorff_space X]
  [the metricType R of real_line_metric R] _ 2 _)=> [|C D].
- by rewrite ler0n.
- rewrite real_line_metric_distanceE compact_hausdorff_distanceE.
  exact: hausdorff_diameter_lipschitz.
Qed.

(** Source for [compact_hyperspace_cost_gap]: supporting
    compactness/positivity step in 2.10.22, p. 185.
    On a compact Hausdorff family, every fixed positive
    diameter threshold has a uniform positive cost gap. *)
Theorem compact_hyperspace_cost_gap (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost)
    (K : set (compact_hausdorff_space X)) (eps : R) :
  compact K -> 0<eps -> exists eta : R, 0<eta /\
    forall C, K C -> cost C<eta -> compact_metric_diameter C<eps.
Proof.
move=> hK heps.
pose H := compact_hausdorff_space X.
pose A : set H := K `&` [set C | eps<=compact_metric_diameter C].
have hlevel : closed [set C : H | eps<=compact_metric_diameter C].
  apply: (@preimage_closed [the topologicalType of H] (real_line_metric R)
    (fun C => compact_metric_diameter C) [set t | eps<=t]).
  - move=> C hC; exact: compact_diameter_map_continuous.
  - exact: closed_ge.
have hA : compact A := compact_closedI hK hlevel.
case: (pselect (A !=set0))=> [hne|hempty].
- have hco : continuous (fun C : H => (cost C : R^o)) := compact_cost_continuous_law hc.
  have hn : continuous (fun C : H => (-cost C : R^o)).
    move=> C; exact: (@continuousN R R^o [the topologicalType of H] (fun D=>cost D) C (hco C)).
  have [D [[hDK hDe] hmin]] := continuous_compact_maximum hne hA hn.
  have hDpos : 0<compact_metric_diameter D := lt_le_trans heps hDe.
  have hpos := @compact_cost_positive_diameter_law R X cost hc D hDpos.
  exists (cost D); split=> // C hCK hsmall.
  case: (ltP (compact_metric_diameter C) eps)=> // hlarge.
  have hCA : A C by split.
  have hh := hmin C hCA; rewrite lerN2 in hh.
  by have := lt_le_trans hsmall hh; rewrite ltxx.
- exists 1; split; first exact: ltr01.
  move=> C hCK hsmall; rewrite ltNge; apply/negP=> hlarge.
  apply: hempty; exists C; by split.
Qed.
