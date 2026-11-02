(** Federer (1969), 3.1.16, p. 228: remove the null exceptional set
    from the almost-everywhere growth hypothesis before applying 3.1.8.
    Undefined quotient inputs remain exceptional, as in 2.9.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanClosedBallVolume EuclideanNoncenteredVitali EuclideanApproximateContext CenteredBallRelations
  CenteredNullSetDensity EuclideanZeroDensityUnion LocalZeroDensity
  ApproximateOrderThresholdRays MeasureApproximateOrderLimits MeasureSetDensity
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  ApproximateMetricGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_approximate_growth_null_restriction]: supporting
    the application of 3.1.8 in Federer 3.1.16, p. 228. Removing a
    Lebesgue-null subset from the actual domain preserves finite
    approximate upper growth at every remaining good point. *)
Lemma finite_approximate_growth_null_restriction (R : realType) m n
    (A N : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) a :
  @euclidean_lebesgue_measure R m N=0%E ->
  (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (partial_metric_growth_quotient A f a) a< +oo)%E ->
  (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (partial_metric_growth_quotient (A `\` N) f a) a< +oo)%E.
Proof.
move=>hN hg.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose mu := @euclidean_lebesgue_measure R m.
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose hc := euclidean_approximate_context R m.
have [q [hqt hq]] := (approximate_upper_limit_rational_ray hc _ a +oo%E).1 hg.
have hzero : partial_function_graph (measure_set_density mu V N) a 0%E.
  apply: centered_null_set_density_zero (euclidean_lebesgue_is_measure R m) _ hN.
  move=>x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
apply: (approximate_upper_limit_rational_ray hc _ a +oo%E).2.
exists q; split=>//.
apply: (@local_zero_density_mono R X mu V
  (~`partial_function_preimage (partial_metric_growth_quotient (A `\` N) f a)
    [set y | (y<=(ratr q : R)%:E)%E])
  ((~`partial_function_preimage (partial_metric_growth_quotient A f a)
    [set y | (y<=(ratr q : R)%:E)%E]) `|` N)
  setT a hc openT I _ (euclidean_zero_density_union hq hzero)).
move=>x _ hbad; case: (pselect (N x))=>[hxN|hxN]; first by right.
left.
move=>[y [hy hsmall]]; apply: hbad; exists y; split=>//.
change ((A x /\ x!=a) /\ (mdist (f x) (f a)/mdist x a)%:E=y) in hy.
change (((A x /\ ~N x) /\ x!=a) /\ (mdist (f x) (f a)/mdist x a)%:E=y).
by split; [split; [split; [exact hy.1.1|exact hxN]|exact hy.1.2]|exact hy.2].
Qed.
