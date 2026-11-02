(** Federer (1969), 2.10.28, p. 191: compare the real power-gauge measure
    with the compact-interval construction. One direction uses each interval
    as an unrestricted nonempty generator with exactly the same cost. This
    supports the power Cantor application on p. 193 and its product example
    in 2.10.29. The coefficient is explicit, before Euler-Gamma
    normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower MetricDiameter CompactIntervalGauge CompactIntervalDiameter
  ConcaveIntervalMeasure MetricRealPowerCost MetricRealPowerMeasureUP MetricRealPowerMeasure
  HausdorffLengthUP CaratheodoryTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_below_interval_measure]: supporting
    unrestricted-cover inequality for the real-line
    claim of 2.10.28, p. 191. All target
    sets are included. The supporting zero
    coefficient case is allowed; the book's
    normalising coefficient is strictly positive. *)
Theorem metric_real_power_below_interval_measure (R : realType) (c p : R) :
  (0<=c)%R -> (0<=p)%R -> forall A : set (real_line_metric R),
  @metric_real_power_measure R [the metricType R of real_line_metric R] c p A<=
    concave_interval_measure (fun x=>(c*real_power x p)%R) A.
Proof.
move=> hc hp A.
pose X := [the metricType R of real_line_metric R].
pose I := compact_real_intervals R.
pose J := @nonempty_metric_sets R X.
pose u (T : I) : J := Sub (val T) (mem_set (compact_real_interval_nonempty (set_valP T))).
have hh : @metric_real_power_measure R X c p (id @` A)<=
    concave_interval_measure (fun x=>(c*real_power x p)%R) A.
  apply: (@caratheodory_limit_transport R X X I J (fun T=>val T) (fun S=>val S)
    (fun T=>(concave_interval_cost (fun x=>(c*real_power x p)%R) (val T))%:E)
    (fun S=>metric_real_diameter_cost c p (val S)) id u
    (concave_interval_measure (fun x=>(c*real_power x p)%R))
    (@metric_real_power_measure R X c p)
    (@concave_interval_measure_specification R (fun x=>(c*real_power x p)%R))
    (@metric_real_power_measure_specification R X c p) _ _ _ _ A).
  - move=> S; exact (@metric_real_power_cost_nonnegative R c p _ hc).
  - by move=> T x hx.
  - by move=> T.
  - move=> T.
    have hD := @compact_interval_diameter_finite_value R (val T) (set_valP T).
    change (is_true (metric_real_diameter_cost c p (val T)<=
      (concave_interval_cost (fun x=>(c*real_power x p)%R) (val T))%:E)).
    by rewrite /metric_real_diameter_cost hD metric_real_power_cost_finite /concave_interval_cost.
by rewrite image_id in hh.
Qed.
