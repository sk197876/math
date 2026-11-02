(** Federer (1969), 2.10.2(1), p. 171: closed nonempty covers give the same
    real power-gauge measure, hence Borel regularity. Keep the normalising
    coefficient explicit for 2.10.29, pp. 193–195. Prove equality from the
    two independent specifications; neither equality nor regularity is a
    defining assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricRealPowerCost MetricRealPowerMeasureUP MetricRealPowerMeasureLaws
  MetricRealPowerMeasure HausdorffLengthUP HausdorffClosedCovers
  MetricDiameter MetricDiameterClosure CaratheodoryTransport BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_closed_cover_agreement]: direct
    unrestricted/closed equality of 2.10.2(1),
    p. 171, for the real power gauge.
    Taking closures preserves both diameter
    and cost; forgetting closedness gives the
    reverse comparison. Repeated closure images
    are handled by the existing cover transport. *)
Theorem metric_real_power_closed_cover_agreement (R : realType) (X : metricType R)
    (c p : R) (mu nu : set X -> \bar R) :
  (0<=c)%R -> is_metric_real_power_measure c p mu ->
  is_closed_metric_real_power_measure c p nu -> forall A, mu A=nu A.
Proof.
move=> hc hm hn A.
have hclosed : nu (id @` A)<=mu A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_metric_sets R X) (@nonempty_closed_metric_sets R X)
    (fun S=>val S) (fun S=>val S)
    (fun S=>metric_real_diameter_cost c p (val S))
    (fun S=>metric_real_diameter_cost c p (val S)) id (@nonempty_closed_hull R X)
    mu nu hm hn _ _ _ _ A).
  - move=> S; exact (@metric_real_power_cost_nonnegative R c p _ hc).
  - move=> S x hx; exact: subset_closure hx.
  - move=> S; change (is_true (extended_metric_diameter (closure (val S))<=extended_metric_diameter (val S))).
    by rewrite extended_metric_diameter_closure.
  - move=> S; change (is_true (metric_real_diameter_cost c p (closure (val S))<=metric_real_diameter_cost c p (val S))).
    by rewrite metric_real_diameter_cost_closure.
have hall : mu (id @` A)<=nu A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_closed_metric_sets R X) (@nonempty_metric_sets R X)
    (fun S=>val S) (fun S=>val S)
    (fun S=>metric_real_diameter_cost c p (val S))
    (fun S=>metric_real_diameter_cost c p (val S)) id (@nonempty_closed_forget R X)
    nu mu hn hm _ _ _ _ A).
  - move=> S; exact (@metric_real_power_cost_nonnegative R c p _ hc).
  - by move=> S x hx.
  - by move=> S.
  - by move=> S.
rewrite image_id in hclosed hall.
by apply/eqP; rewrite eq_le hall hclosed.
Qed.

(** Source for [metric_real_power_closed_measure_equality]: direct
    equality of the independently selected
    measures in 2.10.2(1), p. 171,
    derived only from their opaque specifications. *)
Lemma metric_real_power_closed_measure_equality (R : realType) (X : metricType R) (c p : R) :
  (0<=c)%R -> forall A,
    @metric_real_power_measure R X c p A=@closed_metric_real_power_measure R X c p A.
Proof.
move=> hc; exact (@metric_real_power_closed_cover_agreement R X c p _ _ hc
  (@metric_real_power_measure_specification R X c p)
  (@closed_metric_real_power_measure_specification R X c p)).
Qed.

(** Source for [metric_real_power_measure_borel_regular]: direct
    Borel regularity in 2.10.2(1), p. 171,
    for the actual real power-gauge measure
    with nonnegative coefficient. The proof
    uses the established closed-cover equality. *)
Theorem metric_real_power_measure_borel_regular (R : realType) (X : metricType R) (c p : R) :
  (0<=c)%R -> is_borel_regular_measure (@metric_real_power_measure R X c p).
Proof.
move=> hc.
have he : @metric_real_power_measure R X c p=@closed_metric_real_power_measure R X c p.
  apply: funext=> A; exact (@metric_real_power_closed_measure_equality R X c p hc A).
rewrite he; exact (@closed_metric_real_power_borel_regular_law R X c p _ hc
  (@closed_metric_real_power_measure_specification R X c p)).
Qed.
