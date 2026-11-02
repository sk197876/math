(** Opaque Phi(J,n) witness for Federer (1969), 2.10.28(4), p. 192. Expose
    only the specified interval, radius and spacing laws; keep its finite
    ordinal construction private. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter ConcaveIntervalGaugeUP
  EqualCostIntervalFamilyUP EqualCostIntervalFamilyConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type EQUAL_COST_INTERVAL_FAMILY.
(** Source for [value]: abstract family Phi(J,n)
    in 2.10.28(4), p. 192, for a
    nondegenerate parent and n>=2. *)
Parameter value : forall (R : realType) (h : R -> R), is_concave_interval_gauge h ->
  forall (J : compact_real_intervals R) (n : nat),
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) ->
  (2<=n)%N -> {fset compact_real_intervals R}.
(** Source for [laws]: defining interval, radius
    and spacing laws of Phi(J,n) in
    2.10.28(4), p. 192, from a proved witness. *)
Parameter laws : forall (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
  (J : compact_real_intervals R) (n : nat)
  (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
  (hn : (2<=n)%N), is_equal_cost_interval_family h J n (@value R h hg J n hJ hn).
End EQUAL_COST_INTERVAL_FAMILY.

Module EqualCostIntervalFamily : EQUAL_COST_INTERVAL_FAMILY.
(** Source for [value]: proved finite ordinal-image
    witness for Phi(J,n), 2.10.28(4), p. 192,
    hidden by opaque module ascription. *)
Definition value (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) n
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : (2<=n)%N) := projT1 (cid (@equal_cost_interval_family_exists R h hg J n hJ hn)).
(** Source for [laws]: abstract family laws of
    2.10.28(4), p. 192, proved by
    the encapsulated existence witness. *)
Lemma laws (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) n
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : (2<=n)%N) : is_equal_cost_interval_family h J n (@value R h hg J n hJ hn).
Proof. exact: (projT2 (cid (@equal_cost_interval_family_exists R h hg J n hJ hn))). Qed.
End EqualCostIntervalFamily.
