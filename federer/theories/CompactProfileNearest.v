(** Federer (1969), 2.10.21, p. 183: supporting attainment of distance to a
    nonempty compact set in the Hausdorff and diameter estimates.
    Compactness supplies a minimum of the continuous point-distance
    function. This uses only the existing distance infimum laws and general
    compact extrema. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground CompactSetDistanceProfile MetricSetDistanceUP
  CompactMaximum NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_profile_nearest_point]: supporting
    nearest point to a nonempty compact set in
    2.10.21, p. 183. Convexity, completeness
    and bounded compactness of the ambient space are unnecessary. *)
Theorem compact_profile_nearest_point (R : realType) (X : metricType R)
    (C : compact_metric_set X) (x : X) :
  exists c, val C c /\ mdist x c=compact_set_distance_profile C x.
Proof.
have hf : continuous (fun y : X => (mdist x y : real_line_metric R)).
  apply: (@metric_fixed_lipschitz_continuous R X [the metricType R of real_line_metric R] _ 1 (@ler01 R))=> u v.
  rewrite real_line_metric_distanceE mul1r ler_norml; apply/andP; split.
  - have hh := metric_triangle x u v; lra.
  - have hh := metric_triangle x v u; rewrite (metric_sym v u) in hh; lra.
have hn : continuous (fun y : X => (-mdist x y : R^o)).
  move=> y; exact: (@continuousN R R^o X (fun z=>mdist x z) y (hf y)).
have [c [hc hmax]] := continuous_compact_maximum (set_valP C).2 (set_valP C).1 hn.
exists c; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@metric_set_distance_greatest R X (val C) (compact_set_distance_profile C)
    (compact_set_distance_profile_specification C) x (mdist x c))=> y hy.
  have hh := hmax y hy; by rewrite lerN2 in hh.
- exact: (@metric_set_distance_lower R X (val C) (compact_set_distance_profile C)
    (compact_set_distance_profile_specification C) x c hc).
Qed.
