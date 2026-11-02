(** Opaque recursive-level witness for Federer (1969), 2.10.28, p. 193. Only
    the defining root and child-family laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  EqualCostIntervalTreeUP EqualCostIntervalTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module Type EQUAL_COST_INTERVAL_TREE.
(** Source for [value]: abstract recursive levels
    in 2.10.28, p. 193, for a
    nondegenerate root and schedule n_j>=2. *)
Parameter value : forall (R : realType) (h : R -> R), is_concave_interval_gauge h ->
  forall (J : compact_real_intervals R) (n : nat -> nat),
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) ->
  (forall j, (2<=n j)%N) -> nat -> {fset compact_real_intervals R}.
(** Source for [laws]: root and recursive Phi
    laws of 2.10.28, p. 193,
    proved by the hidden existence witness. *)
Parameter laws : forall (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
  (J : compact_real_intervals R) (n : nat -> nat)
  (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
  (hn : forall j, (2<=n j)%N), is_equal_cost_interval_tree h J n (@value R h hg J n hJ hn).
End EQUAL_COST_INTERVAL_TREE.

Module EqualCostIntervalTree : EQUAL_COST_INTERVAL_TREE.
(** Source for [value]: proved recursive-level
    existence witness for 2.10.28, p. 193,
    hidden by opaque module ascription. *)
Definition value (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) (n : nat -> nat)
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : forall j, (2<=n j)%N) :=
  projT1 (cid (@equal_cost_interval_tree_exists R h hg J n hJ hn)).
(** Source for [laws]: recursive-level specification
    in 2.10.28, p. 193, supplied by
    the encapsulated existence proof. *)
Lemma laws (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) (n : nat -> nat)
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : forall j, (2<=n j)%N) : is_equal_cost_interval_tree h J n (@value R h hg J n hJ hn).
Proof. exact: (projT2 (cid (@equal_cost_interval_tree_exists R h hg J n hJ hn))). Qed.
End EqualCostIntervalTree.
