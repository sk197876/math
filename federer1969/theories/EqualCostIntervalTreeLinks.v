(** Federer (1969), 2.10.29, pp. 193–194: connect the abstract Cantor
    interval trees to their common scalar lengths and child subdivisions.
    Derive these facts from the public recurrence laws; keep the recursive
    witnesses hidden. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  ConcaveIntervalGaugeUP EqualCostIntervalFamilyUP EqualCostIntervalSpecial EqualCostIntervalTreeUP
  EqualCostIntervalTreeLaws EqualCostIntervalUniformWidths InterleavedCantorScalesUP
  SpecialIntervalFamilyUP SpecialIntervalRefinement SpecialIntervalRefinementRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_tree_restricted_children_phi]: supporting
    identification of a parent's actual next-level
    restriction with its specified Phi family
    in 2.10.29, p. 194. Disjointness of
    parents gives the exact restriction; no
    implementation of the recursion is unfolded. *)
Lemma equal_cost_tree_restricted_children_phi (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H (ht : is_equal_cost_interval_tree h J n H) j S :
  S \in H j -> is_equal_cost_interval_family h S (n j)
    (special_interval_restriction (H j.+1) (val S)).
Proof.
move=> hS; have [K [hK he]] := equal_cost_tree_step ht j.
have hlevels := @equal_cost_tree_level_special R h hg J n H ht.
have hKS T hT := @federer_2_10_28_4_special R h hg T (n j) (K T) (hK T hT).
rewrite he (@special_interval_refinement_restriction R h J (H j) K (hlevels j) hKS S hS).
exact: hK S hS.
Qed.

(** Source for [interleaved_left_tree_common_width]: supporting
    equality of every first-factor level-j
    interval length with s_j in 2.10.29,
    pp. 193–194, for the unit root.
    It follows from uniqueness of split
    radii and the two abstract recurrences. *)
Theorem interleaved_left_tree_common_width (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) D (hD : is_interleaved_cantor_scales h D) J H :
  val J=(`[0,1] : set (real_line_metric R)) ->
  is_equal_cost_interval_tree h J (cantor_left_subdivision D) H ->
  forall j S, S \in H j -> fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=
    cantor_left_width D j.
Proof.
move=> hJ ht.
have hroot : cantor_left_width D 0%N=
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
  by rewrite (interleaved_cantor_left_root hD) hJ (extended_metric_diameter_segment ler01) subr0.
exact (@equal_cost_interval_tree_uniform_widths R h hg J (cantor_left_subdivision D) H
  (cantor_left_width D) ht hroot (interleaved_cantor_left_split hD)).
Qed.

(** Source for [interleaved_right_tree_common_width]: supporting
    equality of every second-factor level-j
    interval length with sigma_j in 2.10.29,
    pp. 193–194, under the same abstract
    unit-root and equal-cost recurrence laws. *)
Theorem interleaved_right_tree_common_width (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) D (hD : is_interleaved_cantor_scales h D) J H :
  val J=(`[0,1] : set (real_line_metric R)) ->
  is_equal_cost_interval_tree h J (cantor_right_subdivision D) H ->
  forall j S, S \in H j -> fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=
    cantor_right_width D j.
Proof.
move=> hJ ht.
have hroot : cantor_right_width D 0%N=
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
  by rewrite (interleaved_cantor_right_root hD) hJ (extended_metric_diameter_segment ler01) subr0.
exact (@equal_cost_interval_tree_uniform_widths R h hg J (cantor_right_subdivision D) H
  (cantor_right_width D) ht hroot (interleaved_cantor_right_split hD)).
Qed.
