(** Federer (1969), 2.10.28, p. 193: public equal-cost recursive levels,
    through their abstract sealed laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  EqualCostIntervalTreeUP EqualCostIntervalTreeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [equal_cost_interval_tree]: direct
    recursive levels for A(m,n) in 2.10.28,
    p. 193, generalised to any concave
    gauge and nondegenerate root interval.
    The recursive construction remains hidden. *)
Definition equal_cost_interval_tree (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) (n : nat -> nat)
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : forall j, (2<=n j)%N) := @EqualCostIntervalTree.value R h hg J n hJ hn.

(** Source for [equal_cost_interval_tree_specification]:
    direct root and recursive Phi laws in
    2.10.28, p. 193, obtained only from
    the opaque witness's proved specification. *)
Lemma equal_cost_interval_tree_specification (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) (n : nat -> nat)
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : forall j, (2<=n j)%N) :
  is_equal_cost_interval_tree h J n (@equal_cost_interval_tree R h hg J n hJ hn).
Proof. exact: EqualCostIntervalTree.laws. Qed.
