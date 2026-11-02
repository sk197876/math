(** Federer (1969), 2.10.28(4), p. 192, and Cantor construction p. 193:
    positive child lengths strictly below parent length/n. Derive the mesh
    estimate from the abstract family laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  CantorSplitRadiusUP EqualCostIntervalFamilyUP EqualSpacingIntervalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_child_mesh]: direct
    0<diam(S)<diam(J)/n for S in Phi(J,n),
    2.10.28(4), p. 192. This also
    proves every child can be refined again
    without assuming a nondegenerate-child axiom. *)
Theorem equal_cost_interval_child_mesh (R : realType) (h : R -> R)
    (J : compact_real_intervals R) n F (S : compact_real_intervals R) :
  is_equal_cost_interval_family h J n F -> S \in F ->
  let d := fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) in
  let e := fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)) in
  0<e /\ e<d/n%:R.
Proof.
move=> [_ [a [b [s [t [hJ [hd [hs [ht hchar]]]]]]]]] hS /=.
have [i [hi hval]] := (hchar S).1 hS.
have [hspos hsbound] := cantor_split_radius_bounds hs.
have hab : a<=b by lra.
rewrite hJ hval (extended_metric_diameter_segment hab)
  (equal_spacing_child_diameter a t i%:R (ltW hspos)); by split.
Qed.
