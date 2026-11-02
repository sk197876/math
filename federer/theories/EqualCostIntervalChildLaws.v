(** Federer (1969), 2.10.29, pp. 193–194: propagate the uniform interval
    lengths through the equal-cost Cantor recursion. This supporting
    consequence of 2.10.28(4), p. 192, identifies each child's actual
    diameter with a specified split radius for the parent's actual diameter. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  CantorSplitRadiusUP EqualCostIntervalFamilyUP EqualSpacingIntervalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_child_split_laws]: supporting
    actual diameter recurrence for every child
    in 2.10.29, pp. 193–194, derived
    from the specified Phi intervals in
    2.10.28(4), p. 192. No interval
    implementation or chosen endpoint is exposed. *)
Theorem equal_cost_interval_child_split_laws (R : realType) (h : R -> R)
    (J : compact_real_intervals R) n F (S : compact_real_intervals R) :
  is_equal_cost_interval_family h J n F -> S \in F ->
  is_cantor_split_radius h
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))).
Proof.
move=> [_ [a [b [s [t [hJ [hd [hs [ht hchar]]]]]]]]] hS.
have [i [hi hval]] := (hchar S).1 hS.
have hspos := (cantor_split_radius_bounds hs).1.
have hab : a<=b by lra.
by rewrite hJ hval (extended_metric_diameter_segment hab)
  (equal_spacing_child_diameter a t i%:R (ltW hspos)).
Qed.
