(** Federer (1969), 2.9.22, p. 168: at a Lebesgue point of v the mean of
    |v(t)-v(x)| over nondegenerate intervals containing x tends to zero.
    This supporting lemma extracts that assertion from the exact partial
    Lebesgue-set specification, with actual finite integrals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealConventions
  PartialFunctionUP PartialFunctionBasic MeasureSubsetIntegral LebesgueScalarMeasure
  ScalarIntervalDerivationContext MetricDiameter MetricDiameterReal
  MeasurableDistanceTo MeasureMeanFunction MeasureLebesgueSet CoveringFiniteLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_point_interval_mean_small]: direct
    supporting mean limit in Federer 2.9.22, p. 168,
    second display and its final words. Every sufficiently
    short nondegenerate interval containing x has an actual
    finite distance integral J with J/(b-a)<epsilon. Undefined
    means and degenerate denominators are excluded explicitly. *)
Lemma lebesgue_point_interval_mean_small (R : realType) (Y : metricType R)
    (v : real_line_metric R -> Y) (x : real_line_metric R) :
  (forall a b : R, a<b -> exists J : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (partial_distance_to (partial_function_total v) (v x)) J%:E) ->
  @measure_lebesgue_set R [the metricType R of real_line_metric R] Y
    (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)
    (partial_function_total v) x ->
  forall e : R, 0<e -> exists d : R, 0<d /\ forall a b : R,
    a<b -> a<=x<=b -> b-a<d -> exists J : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (partial_distance_to (partial_function_total v) (v x)) J%:E /\ J/(b-a)<e.
Proof.
move=> hlocal [z [hz hl]] e he.
rewrite -(hz : v x=z) in hl.
have [d [hd hB]] := @covering_finite_limit_small_values R
  [the metricType R of real_line_metric R] (@scalar_nondegenerate_interval_relation R)
  (measure_mean_function (@lebesgue_scalar_measure R)
    (partial_distance_to (partial_function_total v) (v x))) x 0 e hl he.
exists d; split=> // a b hab haxb hwidth.
have [J hJ] := hlocal a b hab.
have hrel : scalar_nondegenerate_interval_relation x `[a,b].
  by exists a,b; split=> //; split.
have hdiam : (@extended_metric_diameter R [the metricType R of real_line_metric R] `[a,b]<d%:E)%E.
  by rewrite (extended_metric_diameter_segment (ltW hab)) lte_fin.
have hpos : 0<b-a by rewrite subr_gt0.
have hden : (@lebesgue_scalar_measure R) `[a,b]=(b-a)%:E.
  exact: lebesgue_scalar_segment (ltW hab).
have hmean : partial_function_graph
    (measure_mean_function (@lebesgue_scalar_measure R)
      (partial_distance_to (partial_function_total v) (v x))) `[a,b] (J/(b-a))%:E.
  exists J%:E; split=> //.
  have hdp : (0<(b-a)%:E :> \bar R)%E by rewrite lte_fin.
  rewrite hden /extended_divide (gt_eqF hdp) /=.
  by rewrite inver (gt_eqF hpos) -EFinM.
have [_ hupper] := hB `[a,b] _ hrel hdiam hmean.
exists J; split=> //.
by move: hupper; rewrite add0r lte_fin.
Qed.
