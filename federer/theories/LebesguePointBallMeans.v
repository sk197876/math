(** Federer (1969), 4.1.2, p. 347: at
    each original Lebesgue point the mean norm error
    on shrinking balls tends to zero, by 2.9.9,
    pp. 156–157. The mean is its actual
    subset integral divided by a positive finite ball mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasureSubsetIntegral
  MeasurableDistanceTo MeasureMeanFunction MeasureLebesgueSet FiniteMeanPartValues
  CoveringFiniteLimitBounds MetricClosedBalls MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [lebesgue_point_ball_mean_small]: the exact
    Lebesgue-point mean limit invoked in Federer 4.1.2,
    p. 347. The covering relation may
    be either the centered or the containing-ball relation;
    each actual centered ball must belong to it. *)
Theorem lebesgue_point_ball_mean_small (R:realType) (X Y:metricType R)
    (mu:set X->\bar R) (V:X->set X->Prop) (f:X->Y) (x:X) (mass:R->R):
  (forall r:R,0<r ->V x (metric_closed_ball x r)) ->
  (forall r:R,0<r ->mu (metric_closed_ball x r)=(mass r)%:E) ->
  (forall r:R,0<r ->0<mass r) ->
  (forall r:R,0<r ->exists J:R,is_measure_subset_integral mu (metric_closed_ball x r)
    (partial_distance_to (partial_function_total f) (f x)) J%:E) ->
  measure_lebesgue_set mu V (partial_function_total f) x ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall r:R,0<r ->r<d ->
    exists J:R,is_measure_subset_integral mu (metric_closed_ball x r)
      (partial_distance_to (partial_function_total f) (f x)) J%:E /\ J/mass r<eta.
Proof.
move=>hBalls hMass hPositive hLocal [y [hy hLimit]] eta hEta.
change (f x=y) in hy; rewrite -hy in hLimit.
have [d [hd hBound]]:=@covering_finite_limit_small_values R X V
  (measure_mean_function mu (partial_distance_to (partial_function_total f) (f x))) x 0 eta hLimit hEta.
exists (d/3); split; first by rewrite divr_gt0 // ltr0n.
move=>r hr hSmall.
have [J hJ]:=@hLocal r hr.
have hMean:=@finite_measure_mean_value R X mu
  (partial_distance_to (partial_function_total f) (f x)) (metric_closed_ball x r) J (mass r)
  hJ (@hMass r hr) (@hPositive r hr).
have hDiameter:(extended_metric_diameter (metric_closed_ball x r)<d%:E)%E.
  have hUpper:(extended_metric_diameter (metric_closed_ball x r)<=(r+r)%:E)%E.
    apply:(metric_diameter_least (extended_metric_diameter_specification _)).
    - rewrite lee_fin; exact:addr_ge0 (ltW hr) (ltW hr).
    - move=>z w hz hw; rewrite lee_fin; exact:metric_closed_ball_diameter_bound hz hw.
  apply:le_lt_trans hUpper _; rewrite lte_fin; lra.
have hUpper:=(hBound (metric_closed_ball x r) (J/mass r)%:E (@hBalls r hr) hDiameter hMean).2.
exists J; split=>//; by move:hUpper; rewrite add0r lte_fin.
Qed.
