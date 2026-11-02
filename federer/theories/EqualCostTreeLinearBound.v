(** Federer (1969), 2.10.29, p. 194: apply the factor-six bound to any
    equal-cost interval tree with a specified scalar width and spacing
    sequence. The hypotheses are only its root and split recurrence laws;
    all level width, child family and measure estimates are derived from
    their abstract interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  ConcaveIntervalMeasure CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalTreeUP
  EqualCostIntervalTreeLaws EqualCostIntervalTreeSpecial EqualCostIntervalTreeLinks EqualCostIntervalUniformWidths
  SpecialIntervalFamilyUP SpecialIntervalUniformLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_tree_uniform_linear_mass_bound]: supporting
    recurrence-level form of the linear mass
    estimate in 2.10.29, p. 194. The
    test length lies between the level's
    subdivision spacing and parent width.
    No chosen tree implementation is unfolded. *)
Theorem equal_cost_tree_uniform_linear_mass_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H (ht : is_equal_cost_interval_tree h J n H)
    A (hA : is_special_interval_tree_limit H A) (q tau : nat -> R) :
  q 0%N=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) ->
  (forall j, is_cantor_split_radius h (q j) (n j) (q j.+1)) ->
  (forall j, tau j=cantor_split_spacing (q j) (n j) (q j.+1)) ->
  forall j (T : compact_real_intervals R),
    tau j<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)) ->
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))<=q j ->
    (concave_interval_measure h (A `&` val T)<=
      (6*h (q j)*fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/q j)%:E)%E.
Proof.
move=> hroot hq htau j T hlarge hsmall.
have hspecial := @equal_cost_interval_tree_special R h hg J n H ht.
have hwidths := @equal_cost_interval_tree_uniform_widths R h hg J n H q ht hroot hq.
have hpos k : 0<q k.
  case: k=> [|i]; last exact: (cantor_split_radius_bounds (hq i)).1.
  rewrite hroot; apply: (@equal_cost_tree_member_positive R h J n H ht 0%N J).
  by rewrite (equal_cost_tree_root ht) in_fset1.
exact (@special_interval_uniform_linear_mass_bound R h hg H hspecial A hA j (n j)
  (q j) (q j.+1) (tau j) T (hpos j) (hwidths j)
  (fun S hS=>@equal_cost_tree_restricted_children_phi R h hg J n H ht j S hS)
  (hq j) (htau j) hlarge hsmall).
Qed.
