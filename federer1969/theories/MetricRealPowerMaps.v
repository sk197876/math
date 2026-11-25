(** Federer (1969), 2.10.11, p. 176, isometric image subcase supporting the
    coordinate regrouping in 2.10.29, p. 195. Prove nonexpanding image
    comparison and isometric equality directly from the real power-gauge
    covering laws. Coefficients and real degrees remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricRealPowerCost MetricRealPowerMeasure HausdorffLengthUP HausdorffLengthMaps
  MetricDiameterUP MetricDiameter MetricDiameterMaps CaratheodoryTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_nonexpanding]: supporting
    nonexpanding real-degree comparison in 2.10.11,
    p. 176, used for the actual orthogonal
    regrouping of 2.10.29, p. 195. No
    measurability premise is needed on A. *)
Theorem metric_real_power_nonexpanding (R : realType) (X Y : metricType R)
    (c p : R) (f : X -> Y) :
  (0<=c)%R -> (0<=p)%R ->
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) -> forall A,
    @metric_real_power_measure R Y c p (f @` A)<= @metric_real_power_measure R X c p A.
Proof.
move=> hc hp hf A.
apply: (@caratheodory_limit_transport R X Y (@nonempty_metric_sets R X) (@nonempty_metric_sets R Y)
  (fun S=>val S) (fun S=>val S)
  (fun S=>metric_real_diameter_cost c p (val S)) (fun S=>metric_real_diameter_cost c p (val S))
  f (@nonempty_metric_image R X Y f) _ _
  (@metric_real_power_measure_specification R X c p) (@metric_real_power_measure_specification R Y c p) _ _ _ _ A).
- move=> S; exact: metric_real_power_cost_nonnegative hc.
- move=> S x hx; by exists x.
- move=> S; exact: extended_metric_diameter_nonexpanding hf (val S).
- move=> S; exact (@metric_real_power_cost_monotone R c p _ _ hc hp
    (metric_diameter_nonnegative (extended_metric_diameter_specification (val (nonempty_metric_image f S))))
    (@extended_metric_diameter_nonexpanding R X Y f hf (val S))).
Qed.

(** Source for [metric_real_power_isometric_image]: supporting
    isometric real-degree image equality for
    2.10.29, p. 195, by the two
    nonexpanding comparisons of 2.10.11, p. 176.
    The inverse and both metric bounds are
    explicit; global surjectivity is unnecessary. *)
Theorem metric_real_power_isometric_image (R : realType) (X Y : metricType R)
    (c p : R) (f : X -> Y) (g : Y -> X) :
  (0<=c)%R -> (0<=p)%R -> cancel f g ->
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) ->
  (forall x y, (mdist (g x) (g y)<=mdist x y)%R) ->
  forall A, @metric_real_power_measure R Y c p (f @` A)= @metric_real_power_measure R X c p A.
Proof.
move=> hc hp hfg hf hg A.
have hupper := metric_real_power_nonexpanding hc hp hf A.
have hlower := metric_real_power_nonexpanding hc hp hg (f @` A).
have he : g @` (f @` A)=A.
  apply/seteqP; split.
  - move=> x [y [a ha <-] <-]; by rewrite hfg.
  - move=> x hx; exists (f x); last exact: hfg.
    by exists x.
rewrite he in hlower; by apply/eqP; rewrite eq_le hupper hlower.
Qed.
